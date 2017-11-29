open preamble

val _ = new_theory "CheckerSpec";

(* Helper functions that have nothing to do with vote counting *)
(* Sum a list of rational numbers *)
val SUM_RAT_def = Define`
  SUM_RAT [] = (0:rat) /\
  SUM_RAT (h::t) = h + SUM_RAT t`;
(* -- *)

(* The main datatypes *)

(* A candidate is represented by a string *)
val _ = Datatype`cand = Cand string`;

(* N.B. A more idiomatic approach might be to use records rather than tuples *)

val _ = type_abbrev("ballots",``:(((cand list) # rat) list)``);
val _ = type_abbrev("tallies",``:(cand,rat) alist``);
val _ = type_abbrev("piles",``:((cand # (((cand list) # rat) list)) list)``);

(* A judgement is a state in the application of the vote counting rules.
   It is either a NonFinal state or a Final state.
*)
val _ = Datatype `
  judgement =
    NonFinal (
     (* ballots    *) ballots #
     (* tallies    *) tallies #
     (* piles      *) piles #
     (* backlog    *) (cand list) #
     (* elected    *) (cand list) #
     (* continuing *) (cand list) )
  | Final
    (* winners *) (cand list)`;

(* The rules *)

(* Each of rule corresponds to a step of vote counting
   A rule is of the following form:
   RULE (qu,st,l) j1 j2
   where
     (parameters of the election)
       qu is the quota (least amount of vote necessary to be elected)
       st is the number of seats
       l  is the list of initial candidates
     (transition step)
       j1 is the judgement before the rule application
       j2 is the judgement after the rule application
*)

val _ = type_abbrev("params",``:rat # num # (cand list)``);

(* EWIN rule *)

val EWIN_def = Define `
  EWIN ((qu,st,l):params) j1 j2 =
    ∃u t p bl e h.
      (j1 = NonFinal (u, t, p, bl, e, h))
      /\ (j2 = Final e)
      /\ ((LENGTH e) = st)`;

(* HWIN rule *)

val HWIN_def = Define `
  HWIN ((qu,st,l):params) j1 j2 =
    ∃u t p bl e h.
       (j1 = NonFinal (u, t, p, bl, e, h))
       /\ (j2 = Final (e++h))
       /\ ((LENGTH (e ++ h)) <= st)`;

(* ELIM_CAND rule *)

val get_cand_tally_def = Define `
  get_cand_tally (c:cand) (ls:tallies) =
    case ALOOKUP ls c of NONE => -1 | SOME r => r`;

val get_cand_pile_def = Define `
  get_cand_pile (c:cand) (ls:piles) =
    case ALOOKUP ls c of NONE => [] | SOME r => r`;

val empty_cand_pile_def = Define `
   (empty_cand_pile (c:cand) ([]:piles) = []) /\
   (empty_cand_pile c (h::t) =
      if (c = FST h) then ((c, []) :: t)
      else h :: (empty_cand_pile c t))`;

val Valid_Init_CandList = Define `
  Valid_Init_CandList (l: cand list) = ((l <> []) /\ ALL_DISTINCT l) `;

val Valid_PileTally = Define `
  Valid_PileTally t (l: cand list) = (!c. (MEM c l) <=> (MEM c (MAP FST t))) `;

val less_than_quota_def = Define `
  less_than_quota qu l ls =
    EVERY (λh. get_cand_tally h l < qu) ls`;

val bigger_than_cand_def = Define `
  bigger_than_cand c t ls =
    EVERY (λh0. get_cand_tally c t <= get_cand_tally h0 t) ls`;

val subpile1_def = Define `
  subpile1 c (p1:piles) p2 ⇔
    EVERY (λp. MEM (if c = FST p then (c,[]) else p) p2) p1`;

val subpile2_def = Define`
  subpile2 c (ps:piles) p1 ⇔
    EVERY (λp. if c = FST p then T else MEM p p1) ps`;

val _ = overload_on("list_MEM",``λl1 l2. set l1 ⊆ set l2``);
val _ = overload_on("list_not_MEM",``λl1 l2. DISJOINT (set l1) (set l2)``);

val equal_except_def = Define `
 ((equal_except (c: cand) l nl ) =
   ?l1 l2.
     (l = l1 ++ l2)
     /\ (nl = l1 ++ [c] ++ l2)
     /\ (~ (MEM c l1))
     /\ (~ (MEM c l2))) `;

val ELIM_CAND_def = Define `
  ELIM_CAND (c:cand) ((qu,st,l):params) j1 j2 =
    ?t p e h nh nba np.
     (j1 = NonFinal ([], t, p, [], e, h))
     /\ Valid_Init_CandList l
     /\ (!c'. MEM c' (h++e) ==> (MEM c' l))
     /\ ALL_DISTINCT (h++e)
     /\ Valid_PileTally p l
     /\ Valid_PileTally np l
     /\ LENGTH (e ++ h) > st
     /\ LENGTH e < st
     /\ ALL_DISTINCT (MAP FST t)
     /\ Valid_PileTally t l
     /\ (!c'. (MEM c' h ==> (?x. MEM (c',x) t /\ ( x < qu))))
     /\ MEM c h
     /\ (!d. (MEM d h ==> (?x y. (MEM (c,x) t) /\ (MEM (d,y) t) /\ ( x <= y))))
     /\ equal_except c nh h
     /\ (nba = get_cand_pile c p)
     /\ MEM (c,[]) np
     /\ (!d'. ((d' <> c) ==> (!l. (MEM (d',l) p ==> MEM (d',l) np)
                               /\ (MEM (d',l) np ==> MEM (d',l) p))))
     /\ (j2 = NonFinal (nba, t, np, [], e, nh))`;

(* TRANSFER rule *)

val TRANSFER_def = Define `
  TRANSFER ((qu,st,l):params) j1 j2 =
    ? nba t p bl e h nbl np.
     (j1 = NonFinal ([], t, p, bl, e, h))
     /\ (LENGTH e < st)
     /\ (!d. MEM d (h++e) ==> MEM d l)
     /\ ALL_DISTINCT (h++e)
     /\ (Valid_PileTally t l)
     /\ (Valid_PileTally p l)
     /\ (Valid_PileTally np l)
     /\ (Valid_Init_CandList l)
     /\ ALL_DISTINCT (MAP FST t)
     /\ (!c'. (MEM c' h ==> (?x. MEM (c',x) t /\ ( x < qu))))
     /\ ? l c.
              ((bl = c::l)
           /\ (nbl = l)
           /\ (nba = get_cand_pile c p)
           /\ (MEM (c,[]) np)
           /\ (!d'. ((d' <> c) ==> (!l'. (MEM (d',l') p ==> MEM (d',l') np)
                            /\ (MEM (d',l') np ==> MEM (d',l') p)))))
           /\ (j2 = NonFinal (nba, t, np, nbl, e, h))`;

(* COUNT rule *)

val first_continuing_cand_def = Define `
   first_continuing_cand (c: cand) (b: cand list)  (h: cand list) =
      (?l1 l2. (b = l1 ++ c::l2) /\ (!d. MEM d l1 ==> ~ MEM d h))`;

val COUNT_def = Define	`
  COUNT ((qu,st,l):params) j1 j2 =
    ? ba t nt p np bl e h.
        (j1 = NonFinal (ba, t, p, bl, e, h))
     /\ (!d. MEM d (h++e) ==> MEM d l)
     /\ ALL_DISTINCT (h++e)
     /\ (Valid_PileTally t l)
     /\ (Valid_PileTally nt l)
     /\ (Valid_PileTally p l)
     /\ (Valid_PileTally np l)
     /\ (Valid_Init_CandList l)
     /\ ALL_DISTINCT (MAP FST t)
     /\ (!c. ~ MEM c h ==> MEM c l)
     /\ (ba <> [])
     /\ (!c. ((MEM c h ==>
                           ?(l: ((cand list) # rat) list).
                             (l = FILTER (\ (b: (cand list) # rat). (first_continuing_cand c (FST b) h)) ba)
                          /\ (!l'. MEM (c,l') np ==> (l' = (get_cand_pile c p) ++ l))
                          /\ (!r. MEM (c,r) nt ==> (r = SUM_RAT (MAP SND l))))
                         /\ (~ MEM c h ==>
                                         (!l'. MEM (c,l') np <=> MEM (c,l') p)
                                      /\ (!r. MEM (c,r) t <=> MEM (c,r) nt))))
     /\ (j2 = NonFinal ([], nt, np, bl, e, h))`;

(* ELECT rule *)

val tally_comparison_def = Define `
  tally_comparison (t:tallies) c1 c2 ⇔ (get_cand_tally c1 t <= get_cand_tally c2 t)`;

val update_cand_trans_val_def = Define `
    (update_cand_trans_val (qu:rat) (c:cand) (t:tallies) (p:piles) =
        MAP (λr. r * (((get_cand_tally c t) - qu) / (get_cand_tally c t)))
          (MAP SND (get_cand_pile c p)))`;

val ELECT_def = Define `
  ELECT ((qu,st,l):params) j1 j2 =
  (? t p bl e h nh ne np nbl l1 .
    (j1 = NonFinal ([], t, p, bl, e, h))
    /\ (l1 <> [])
    /\ (SORTED (tally_comparison t) l1)
    /\ (!c. MEM c l1 ==> (!(r :rat). MEM (c,r) t ==> (qu <= r)))
    /\ (LENGTH (l1 ++ e) <= st)
    /\ (!c. MEM c l1 \/ MEM c nh ==> MEM c h)
    /\ (!c. MEM c h ==> MEM c nh \/ MEM c l1)
    /\ ALL_DISTINCT h
    /\ ALL_DISTINCT (l1 ++ nh)
    /\ ALL_DISTINCT (l1 ++ e)
    /\ ALL_DISTINCT ne
    /\ (!c. MEM c l1 \/ MEM c e ==> MEM c ne)
    /\ (!c. MEM c ne ==> MEM c e \/ MEM c l1)
    /\ (!c. MEM c h /\ (~ MEM c l1) ==> (!l'. MEM (c,l') np <=> MEM (c,l') p))
    /\ ALL_DISTINCT (MAP FST p)
    /\ ALL_DISTINCT (MAP FST t)
    /\ ALL_DISTINCT (MAP FST np)
    /\ (!c. MEM c l1 ==> (!l'. MEM (c,l') np ==>
                             (MAP FST l' = MAP FST (get_cand_pile c p))
                          /\ (MAP SND l' = update_cand_trans_val qu c t p)))
    /\ (nbl = bl ++ l1)
    /\ (Valid_Init_CandList l)
    /\ (Valid_PileTally t l)
    /\ (Valid_PileTally p l)
    /\ (Valid_PileTally np l)
    /\ (!c. MEM c ne ==> MEM c l)
    /\ (!c. MEM c h ==> MEM c l)
    /\ (j2 = NonFinal ([], t, np, nbl, ne, nh)))`;

(* Initial judgement *)

val initial_judgement_def = Define `
   initial_judgement (l: cand list) j =
     ? ba t p bl e h.
     (j = NonFinal (ba, t, p, bl, e, h))
     /\ (!c. MEM c (MAP SND t) ==> (c = 0))
     /\ (!c. MEM c (MAP SND p) ==> (c = []))
     /\ (bl = [])
     /\ (e = [])
     /\ (h = l)`;

(* Valid list of judgements *)

val valid_judgements_def =  Define `
 valid_judgements params J ⇔
   (J <> []) /\ (∃w. LAST J = Final w)
   /\ (! J0 J1 j0 j1.
         (J = J0 ++ [j0;j1]++ J1) ==>
           ((HWIN params j0 j1)
           \/ (EWIN params j0 j1)
           \/ (COUNT params j0 j1)
           \/ (TRANSFER params j0 j1)
           \/ (ELECT params j0 j1)
           \/ (?c. MEM c (SND(SND params)) /\ ELIM_CAND c params j0 j1)))`;

(* N.B. A more idiomatic approach might be:

val (valid_step_rules,valid_step_ind,valid_step_cases) = Hol_reln`
  (HWIN params j0 j1 ==> valid_step params j0 j1) ∧
  (EWIN params j0 j1 ==> valid_step params j0 j1) ∧
  (COUNT params j0 j1 ==> valid_step params j0 j1) ∧
  (TRANSFER params j0 j1 ==> valid_step params j0 j1) ∧
  (ELECT params j0 j1 ==> valid_step params j0 j1) ∧
  (MEM c (SND(SND params)) ∧ ELIM_CAND c params j0 j1 ==> valid_step params j0 j1)`;

val valid_steps_def = Define`
  valid_steps params J ⇔
    ∃st w. LRC (valid_step params) J (NonFinal st) (Final w)`;
*)

(* Valid certificate *)

val valid_certificate_def = Define`
  valid_certificate ((qu,st,l):params) J ⇔
    initial_judgement l (HD J) ∧
    valid_judgements (qu,st,l) J`;

val _ = export_theory();
