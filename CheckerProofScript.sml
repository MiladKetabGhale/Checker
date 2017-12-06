open preamble CheckerSpecTheory CheckerTheory
open ratTheory

val _ = new_theory "CheckerProof";

val list_MEM_dec_thm = Q.store_thm("list_MEM_dec_thm",
  `list_MEM_dec = list_MEM`,
  simp[FUN_EQ_THM]
  \\ Induct \\ rw[list_MEM_dec_def]);


val EWIN_thm = Q.store_thm("EWIN_thm",
  `EWIN_dec = EWIN`,
  simp[FUN_EQ_THM]
  \\ qx_gen_tac`params`
  \\ PairCases_on`params`
  \\ Cases \\ Cases
  \\ rw[EWIN_def,EWIN_dec_def]
  \\ PairCases_on`p`
  \\ rw[EWIN_def,EWIN_dec_def]
  \\ metis_tac[]);

val HWIN_thm = Q.store_thm("HWIN_thm",
  `HWIN_dec = HWIN`,
  simp[FUN_EQ_THM]
  \\ qx_gen_tac`params`
  \\ PairCases_on`params`
  \\ Cases \\ Cases \\ rw[HWIN_def,HWIN_dec_def]
  \\ PairCases_on`p`
  \\ rw[HWIN_def,HWIN_dec_def]
  \\ metis_tac[HWIN_def,HWIN_dec_def])

val GET_CAND_TALLY_HEAD_REMOVAL_def = Q.store_thm ("GET_CAND_TALLY_HEAD_REM",
`!(h: cand #rat) t c. (~(c = FST h)) ==> (get_cand_tally c (h::t) = get_cand_tally c t)`,
          Induct_on `t `
               >- (rw[get_cand_tally_def] >>
                   Cases_on`h` >> fs[ALOOKUP_def])

               >- (REPEAT STRIP_TAC
                 >> first_assum (qspecl_then [`h`,`c`] strip_assume_tac)
                    >> rw[get_cand_tally_def] >>
                    Cases_on`h'` >> fs[ALOOKUP_def]))

val GET_CAND_TALLY_MEM = Q.store_thm ("GET_CAND_TALLY_MEM",
 `!(t: (cand #rat) list) c. (MEM c (MAP FST t))
                                    ==> (MEM (c, get_cand_tally c t) t) `,

    Induct_on `t`
        >- rw []

        >- ((REPEAT STRIP_TAC >> Cases_on `h` >> Cases_on `c =q`)
          >- fs[get_cand_tally_def,ALOOKUP_def]
	  >- fs[get_cand_tally_def,ALOOKUP_def]));

(*
val Legal_to_legal_tally_cand = Q.store_thm("Legal_to_legal_tally_cand",
   `!l  (t: (Cand # rat) list) c. (Legal_Tally_Cand l t c) ==> (legal_tally_cand l t c) `,

     Induct_on `t`
       >- ASM_SIMP_TAC bool_ss [Legal_Tally_Cand_def, legal_tally_cand_def]
       >- ((ASSUME_TAC CAND_EQ_DEC
         >> STRIP_TAC
          >> STRIP_TAC
           >> STRIP_TAC
            >> first_assum (qspecl_then [`c`,`FST h`] strip_assume_tac))
              >- (RW_TAC bool_ss [Legal_Tally_Cand_def, legal_tally_cand_def]
                >> MAP_EVERY qexists_tac [`[]`, `SND h`,`t`]
                  >> rw[])
              >- (first_assum (qspecl_then [`l`,`c`] strip_assume_tac)
                >> FULL_SIMP_TAC bool_ss [Legal_Tally_Cand_def, legal_tally_cand_def]
                 >> STRIP_TAC
                   >> FULL_SIMP_TAC bool_ss []
                     >> MAP_EVERY qexists_tac [`h::l1`,`x`,`l2`]
                      >> rw[]))) ;

val legal_to_Legal_tally_cand = Q.store_thm ("legal_to_Legal_tallt_cand",
    `!l (t: (Cand # rat) list) c. (legal_tally_cand l t c) ==> (Legal_Tally_Cand l t c) `,

      Induct_on `t`
        >- rw[legal_tally_cand_def, Legal_Tally_Cand_def]

          >- ((STRIP_TAC
           >> STRIP_TAC
            >> STRIP_TAC
             >> ASSUME_TAC CAND_EQ_DEC
              >> first_assum (qspecl_then [`c`,`FST h`] strip_assume_tac))
          >- ((RW_TAC bool_ss [legal_tally_cand_def, Legal_Tally_Cand_def]
            >> ASSUME_TAC (INST_TYPE [alpha |-> ``:(Cand #rat)``] list_nchotomy)
              >> first_assum (qspecl_then [`l1`] strip_assume_tac))
                >- FULL_SIMP_TAC bool_ss [APPEND,APPEND_NIL,CONS_11]
                >- (FULL_SIMP_TAC bool_ss [APPEND,CONS_11]
                  >> rw []
                    >> FULL_SIMP_TAC bool_ss [MEM,MAP]))
        >- ((STRIP_TAC
          >> RW_TAC bool_ss [legal_tally_cand_def,Legal_Tally_Cand_def])
             >- FULL_SIMP_TAC bool_ss [legal_tally_cand_def]
             >- ((first_assum (qspecl_then [`l`,`c`] strip_assume_tac)
               >> FULL_SIMP_TAC bool_ss [legal_tally_cand_def]
                 >> ASSUME_TAC (INST_TYPE [alpha |-> ``:(Cand #rat)``] list_nchotomy)
                   >> first_assum (qspecl_then [`l1`] strip_assume_tac))
                     >- FULL_SIMP_TAC bool_ss [APPEND,APPEND_NIL,CONS_11,FST]
                     >- (rw []
                       >> FULL_SIMP_TAC bool_ss [APPEND,CONS_11,MAP,MEM]
                         >> rw []
                           >> METIS_TAC []))))) ;
*)

val PileTally_to_PileTally_DEC1 = Q.store_thm ("PileTally_to_PileTally_DEC1",
 `!l t. (!c. (MEM c (MAP FST t)) ==> (MEM c l)) ==> (Valid_PileTally_dec1 t l) `,

    Induct_on `t`
       >- rw [Valid_PileTally_dec1_def]
       >- (REPEAT STRIP_TAC
          >> first_assum (qspecl_then [`FST h`] strip_assume_tac)
            >> rfs[Valid_PileTally_dec1_def,MAP]));

val PileTally_DEC1_to_PileTally = Q.store_thm ("PileTally_DEC1_to_PileTally",
 `!l t. (Valid_PileTally_dec1 t l) ==> (!c. MEM c (MAP FST t) ==> (MEM c l))`,

    Induct_on `t`
        >- rw[]
        >- (REPEAT STRIP_TAC
            >> rfs [Valid_PileTally_dec1_def]));

(*
val non_empty_IS_CORRECT = Q.store_thm ("non_empty_IS_CORRECT",
  `!(l: (Cand # rat) list). (non_empty l) ==> (?l0 ls. (l = l0::ls)) `,

     (STRIP_TAC
       >> ASSUME_TAC (INST_TYPE [alpha |-> ``:Cand #rat``] list_nchotomy)
         >> first_assum (qspecl_then [`l`] strip_assume_tac))
            >- rw [non_empty]
            >- rw[non_empty]);

*)



val PileTally_to_PileTally_DEC2 = Q.store_thm ("PileTally_to_PileTally_DEC2",
   `!l t. (!c. (MEM c l) ==> (MEM c (MAP FST t))) ==> (Valid_PileTally_dec2 t l) `,

     Induct_on `l`
        >- rw [Valid_PileTally_dec2_def]
        >- rfs [Valid_PileTally_dec2_def]);


val PileTally_DEC2_IMP_PileTally = Q.store_thm ("PileTally_DEC2_IMP_PileTally",
  `!l t. (Valid_PileTally_dec2 t l) ==> (!c. (MEM c l) ==> (MEM c (MAP FST t)))`,

      Induct_on `l`
         >- rw []
         >- ((REPEAT STRIP_TAC
           >> FULL_SIMP_TAC list_ss [MEM])
              >- FULL_SIMP_TAC list_ss [Valid_PileTally_dec2_def]
              >- rfs [Valid_PileTally_dec2_def]));


val REMOVE_ONE_CAND_APPEND = Q.store_thm ("REMOVE_ONE_CAND_APPEND",
 `! l1 l2 (c: cand). (~ MEM c l1) ==> (equal_except_dec c (l1 ++l2) = l1 ++ (equal_except_dec c l2))`,

   Induct_on `l1`
       >- RW_TAC list_ss [APPEND_NIL,equal_except_dec_def]
       >- (REPEAT STRIP_TAC
         >> first_assum (qspecl_then [`l2`,`c`] strip_assume_tac)
           >> FULL_SIMP_TAC list_ss [MEM,equal_except_dec_def]));


val REMOVE_ONE_CAND_NOTIN = Q.store_thm ("REMOVE_ONE_CAND_NOTIN",
 `!l (c: cand). (~ MEM c l) ==> (equal_except_dec c l = l) `,

    Induct_on `l`
        >- rw [equal_except_dec_def]
        >- (REPEAT STRIP_TAC
          >> FULL_SIMP_TAC list_ss [MEM, equal_except_dec_def])) ;



val EQE_REMOVE_ONE_CAND = Q.store_thm ("EQE_REMOVE_ONE_CAND",
  `!h (c: cand). (MEM c h) /\ (ALL_DISTINCT h) ==> (equal_except c (equal_except_dec c h) h) `,

 Induct_on `h`

   >-  rw[]

   >-  ((REPEAT STRIP_TAC
      >> Cases_on `c= h'`)

         >- (rw[equal_except_dec_def,equal_except_def]
          >> MAP_EVERY qexists_tac [`[]`,`h`]
	  >> FULL_SIMP_TAC list_ss [ALL_DISTINCT])

        >-  ((rw[equal_except_dec_def,equal_except_def]
           >> `ALL_DISTINCT h` by fs[ALL_DISTINCT]
            >> `equal_except c (equal_except_dec c h) h` by metis_tac [ALL_DISTINCT,MEM]
             >> rfs[equal_except_def])

              >-  rw[]

              >- (MAP_EVERY qexists_tac [`h'::l1`,`l2`]
                >> FULL_SIMP_TAC list_ss []))));


val EQE_IMP_REMOVE_ONE_CAND = Q.store_thm ("EQE_IMP_REMOVE_ONE_CAND",
 `!h1 h2 (c: cand). (MEM c h2) /\ (equal_except c h1 h2) ==> (h1 = equal_except_dec c h2) `,

   FULL_SIMP_TAC list_ss [equal_except_def]
    >> REPEAT STRIP_TAC
     >>  ASSUME_TAC REMOVE_ONE_CAND_APPEND
         >> first_assum (qspecl_then [`l1`,`[c]++l2`,`c`] strip_assume_tac)
             >> rfs [equal_except_dec_def]);


val APPEND_NIL_LEFT = Q.store_thm ("APPEND_NIL_LEFT",
                                                `!l. [] ++ l = l `,
                                                       STRIP_TAC >> EVAL_TAC) ;

val APPEND_NIL_LEFT_COR = Q.store_thm("APPEND_NIL_lEFT_COR",
                                             `!h t. [] ++ (h::t) = h::t `,
                                                   rw[APPEND_NIL_LEFT]) ;



val MAP_APPEND_TRIO = Q.store_thm ("MAP_APPEND_TRIO",
  `!t l1 l0 l2. (t = l1 ++ [l0] ++ l2) ==> (MAP FST t = (MAP FST l1) ++ [FST l0] ++ (MAP FST l2))`,

     REPEAT STRIP_TAC
          >> `l1 ++ [l0] ++ l2 = l1 ++([l0] ++ l2)` by FULL_SIMP_TAC list_ss [APPEND_ASSOC]
            >> RW_TAC bool_ss []
              >> rfs [MAP_APPEND]);



val NoDupCand_BOTH_SIDES= Q.store_thm ("NoDupCand_BOTH_SIDES",
 `!l1 l2 (c:cand) (h1: cand list) h2. (l1 ++ [c] ++ l2 = h1 ++ [c] ++ h2)
                                      /\ (~ MEM c h1) /\ (~ MEM c h2) ==> (~ MEM c l1) `,

    Induct_on `l1`
         >- rw []
         >- ((REPEAT STRIP_TAC >>
               Cases_on `h1`)

               >-   (rfs[APPEND,CONS_11]
                    >> RW_TAC bool_ss []
                      >> rfs[])

               >-   (rfs[CONS_11]
                    >> first_assum (qspecl_then [`l2`,`c`,`t`,`h2`] strip_assume_tac)
                      >> rfs[])));





val get_cand_tally_APPEND = Q.store_thm ("get_cand_tally_APPEND",
  `!(l1: (cand #rat) list) l2 c. (~ MEM c (MAP FST l1))
                                  ==> (get_cand_tally c (l1++l2) = get_cand_tally c l2) `,

      Induct_on `l1`
           >- rw[APPEND_NIL,get_cand_tally_def] >>
	      Cases_on `h`
           >- (REPEAT STRIP_TAC >>
               `c <> q` by fs[MEM,MAP] >>
               fs[get_cand_tally_def,ALOOKUP_def]))



val EVERY_CAND_HAS_ONE_TALLY = Q.store_thm ("EVERY_CAND_HAS_ONE_TALLY",
  `!t c (x: rat). (ALL_DISTINCT (MAP FST t)) /\ (MEM (c,x) t) ==> (get_cand_tally c t = x) `,

      REPEAT STRIP_TAC
           >>  FULL_SIMP_TAC list_ss [MEM_SPLIT]
               >>
               ASSUME_TAC (INST_TYPE [alpha |-> ``:cand``] ALL_DISTINCT_APPEND)
               >> first_assum (qspecl_then [`MAP FST l1`,`MAP FST ([(c,x)] ++ l2)`] strip_assume_tac)
               >> `ALL_DISTINCT ((MAP FST l1) ++ (MAP FST ([(c,x)] ++ l2)))`
	        by FULL_SIMP_TAC list_ss [ALL_DISTINCT_APPEND, MAP_APPEND]
               >> `!e. MEM e (MAP FST l1) ==> (~ MEM e (MAP FST ([(c,x)] ++ l2)))` by metis_tac[]
               >> `MEM c (MAP FST ([(c,x)] ++ l2))` by FULL_SIMP_TAC list_ss [MAP_APPEND]
               >> `~ MEM c (MAP FST l1)` by metis_tac[]
	       >> fs[get_cand_tally_APPEND,get_cand_tally_def,ALOOKUP_def])



val LESS_THAN_QUOTA_OK = Q.store_thm ("LESS_THAN_QUOTA_OK",
`!qu t0 t1 h. (less_than_quota qu (t0::t1) h) ==> (!c.(MEM c h) ==> (get_cand_tally c (t0::t1) < qu))`,

    Induct_on `h`
       >- rw []
       >- (REPEAT STRIP_TAC
         >> FULL_SIMP_TAC list_ss [MEM,less_than_quota_def,get_cand_tally_def]));


val less_than_qu_IMP_LogicalLessThanQuota = Q.store_thm ("less_than_qu_IMP_LogicalLessThanQuota",
 `!h t0 t1 (qu:rat). (less_than_quota qu (t0::t1) h) /\ (Valid_PileTally_dec2 (t0::t1) h) ==>
           (!c. (MEM c h) ==> ?x. (MEM (c,x) (t0::t1)) /\ (x < qu))`,

       Induct_on `h`
          >- rw []
          >- ((REPEAT STRIP_TAC
            >> FULL_SIMP_TAC bool_ss [MEM])
             >- ((ASSUME_TAC (INST_TYPE [alpha |-> ``:rat``] PileTally_DEC2_IMP_PileTally)
                >> first_x_assum (qspecl_then [`h'::h`,`t0::t1`] strip_assume_tac)
                  >> `!c. MEM c (h'::h) ==> (MEM c (MAP FST (t0::t1))) ` by metis_tac []
                     >> `!(h: (cand#rat)) t c. (MEM c (MAP FST (h::t)))
                                 ==> (MEM (c,get_cand_tally c (h::t)) (h::t))`
                        by (ASSUME_TAC GET_CAND_TALLY_MEM2
                         >> REPEAT STRIP_TAC
                         >> first_x_assum (qspecl_then [`h''::t`,`c'`] strip_assume_tac)
                         >> rw [])
                          >> first_assum (qspecl_then [`h'`] strip_assume_tac)
                            >> first_assum (qspecl_then [`t0`,`t1`,`h'`] strip_assume_tac) >> rfs[])
                             >- (qexists_tac `get_cand_tally h' (t0::t1)`
                               >> rfs [less_than_quota_def])
                             >- (qexists_tac `get_cand_tally h' (t0::t1)`
                              >> rw [] >> ASSUME_TAC LESS_THAN_QUOTA_OK
                               >> first_x_assum (qspecl_then [`qu`,`t0`,`t1`,`c::h`] strip_assume_tac)
                                >> rfs []))
             >- (first_assum (qspecl_then [`t0`,`t1`,`qu`] strip_assume_tac)
               >> rfs [less_than_quota_def,Valid_PileTally_dec2_def])));


val LogicalLessThanQu_IMP_less_than_quota =Q.store_thm ("LogicalLessThanQu_IMP_less_than_quota",
  `!(qu:rat) t h. (!c. (MEM c h) ==> ?x. (MEM (c,x) t)
                                       /\ (x < qu)) /\ (ALL_DISTINCT (MAP FST t))
                                       /\ (!c''. (MEM c'' h) ==> (MEM c'' (MAP FST t)))
                                   ==> (less_than_quota qu t h)`,

   Induct_on `h`
     >- rw [less_than_quota_def]
     >- ((REPEAT STRIP_TAC >>
        rw[less_than_quota_def])
          >- (`?x. (MEM (h',x) t) /\ (x < qu)` by metis_tac[MEM]
           >> `MEM h' (MAP FST t)` by metis_tac[MEM]
             >> `MEM (h', get_cand_tally h' t) t` by metis_tac [GET_CAND_TALLY_MEM2]
                 >> ASSUME_TAC EVERY_CAND_HAS_ONE_TALLY
                 >> `get_cand_tally h' t = x` by rfs [EVERY_CAND_HAS_ONE_TALLY]
                   >> metis_tac [])
        >- (`less_than_quota qu t h` by  metis_tac[MEM]
           >> fs[less_than_quota_def])))


val bigger_than_cand_OK = Q.store_thm ("bigger_than_cand_OK",
 `!c t h. (bigger_than_cand c t h) ==> (!d. (MEM d h) ==> (get_cand_tally c t <= get_cand_tally d t))`,

      Induct_on `h`
          >- rw []
          >- (REPEAT STRIP_TAC
            >> FULL_SIMP_TAC list_ss [MEM,bigger_than_cand_def]));



val bigger_than_cand_LogicallyOK = Q.store_thm ("bigger_than_cand_LogicallyOK",
 `!h (t0: cand #rat) t1 c. (bigger_than_cand c (t0::t1) h)
                        /\ (Valid_PileTally_dec2 (t0::t1) h) /\ (MEM c h) ==>
   (!d. (MEM d h)  ==> (?x (y: rat). (MEM (c,x) (t0::t1)) /\ (MEM (d,y) (t0::t1)) /\ (x <= y)))`,

     Induct_on `h`
        >- rw []
        >- (REPEAT STRIP_TAC
          >> ASSUME_TAC (INST_TYPE [alpha |-> ``:rat``] PileTally_DEC2_IMP_PileTally)
            >> first_assum (qspecl_then [`h'::h`,`t0::t1`] strip_assume_tac)
              >> `!c'. (MEM c' (h'::h)) ==> (MEM c' (MAP FST (t0::t1)))` by metis_tac []
                >> first_assum (qspecl_then [`c`] strip_assume_tac)
                  >> first_assum (qspecl_then [`d`] strip_assume_tac)
                    >> `MEM (c,get_cand_tally c (t0::t1)) (t0::t1)` by rfs [GET_CAND_TALLY_MEM2,MEM]
                      >> `MEM (d,get_cand_tally d (t0::t1)) (t0::t1)` by rfs [GET_CAND_TALLY_MEM2,MEM]
                       >> MAP_EVERY qexists_tac [`get_cand_tally c (t0::t1)`,`get_cand_tally d (t0::t1)`]
                         >> RW_TAC list_ss []
                           >> ASSUME_TAC bigger_than_cand_OK
                             >> first_assum (qspecl_then [`c`,`t0::t1`,`h'::h`] strip_assume_tac)
                               >> metis_tac []));





val Logical_bigger_than_cand_IMP_TheFunctional = Q.store_thm ("Logical_bigger_than_cand_IMP_TheFunctional",
 `!h t c. (!d. (MEM d h)  ==> (?x (y: rat). (MEM (c,x) t)
                                                  /\ (MEM (d,y) t) /\ (x <= y)))
                                                  /\ (ALL_DISTINCT (MAP FST t))
                                                  /\ (MEM c (MAP FST t))
                                                  /\ (!d''. (MEM d'' h) ==> (MEM d'' (MAP FST t)))
                                                 ==> (bigger_than_cand c t h)`,

    Induct_on `h`
        >- rw [bigger_than_cand_def]
        >- ((REPEAT STRIP_TAC
             >> rw[bigger_than_cand_def])
               >-( `?x y. (MEM (c,x) t) /\ (MEM (h',y) t) /\ (x <= y) ` by metis_tac [MEM]
                >> `MEM c (MAP FST t)` by metis_tac [MEM]
                 >> `MEM (c,get_cand_tally c t) t` by metis_tac [GET_CAND_TALLY_MEM2]
                   >> ASSUME_TAC EVERY_CAND_HAS_ONE_TALLY
                   >> `x = get_cand_tally c t` by rfs []
                    >> `MEM h' (MAP FST t)` by metis_tac [MEM]
                     >> `MEM (h',get_cand_tally h' t) t` by metis_tac [GET_CAND_TALLY_MEM2]
                      >> `y = get_cand_tally h' t ` by rfs []
                       >> RW_TAC bool_ss [])
             >-( first_assum(qspecl_then [`t`,`c`] strip_assume_tac)
               >> rfs[bigger_than_cand_def,MEM])));



val SUBPILE_ONE_HEAD_REMOVAL = Q.store_thm ("SUBPILE_ONE_HEAD_REMOVAL",
 `! p1 p2 c h. (subpile1 c (h::p1) p2) ==> (subpile1 c p1 p2)`,
  rw[subpile1_def]);


val Functional_subpile1_IMP_TheLogical = Q.store_thm ("Functional_subpile1_IMP_TheLogical",
 `!p1 p2 c. (subpile1 c p1 p2) ==>  (!d'. ((d' <> c) ==> (!l. (MEM (d',l) p1 ==> MEM (d',l) p2))))`,

     Induct_on `p1`
        >- rw[]
        >- ((REPEAT STRIP_TAC
          >> FULL_SIMP_TAC list_ss [MEM])
            >- (`d' = FST h` by RW_TAC bool_ss [PAIR_EQ,FST]
              >> `c <> FST h` by RW_TAC bool_ss []
                >> FULL_SIMP_TAC list_ss [subpile1_def])
            >- (first_assum (qspecl_then [`p2`,`c`] strip_assume_tac)
              >> metis_tac[SUBPILE_ONE_HEAD_REMOVAL])));


val GET_CAND_PILE_MEM = Q.store_thm ("GET_CAND_PILE_MEM",
 `!(p:(cand # (((cand list) # rat) list)) list) c. (MEM c (MAP FST p))
                          ==> (MEM (c,get_cand_pile c p) p)`,

        Induct_on `p`
             >-  rw []
               >- ((REPEAT STRIP_TAC
                 >>Cases_on `c = FST h`)

                 >- (Cases_on `h`
                   >> fs[get_cand_pile_def,ALOOKUP_def,MEM])

                 >- (Cases_on `h`
                   >> rfs [get_cand_pile_def,ALOOKUP_def,MEM,MAP]
                     >> rw[])));


val get_cand_pile_APPEND = Q.store_thm ("get_cand_pile_APPEND",
 `! (l1:(cand # (((cand list) # rat) list)) list) l2 c. (~ MEM c (MAP FST l1))
                           ==> (get_cand_pile c (l1++l2) = get_cand_pile c l2)`,

     Induct_on `l1`
        >-  rw []
        >- (REPEAT STRIP_TAC >>
	      Cases_on `h` >> FULL_SIMP_TAC list_ss [ALOOKUP_def,MEM,MAP,get_cand_pile_def]));



val EVERY_CAND_HAS_ONE_PILE = Q.store_thm ("EVERY_CAND_HAS_ONE_PILE",
 `! p c (y: ((cand list) # rat) list). (ALL_DISTINCT (MAP FST p)) /\ (MEM (c,y) p)
                          ==> (get_cand_pile c p = y)`,

      (REPEAT STRIP_TAC
      >> FULL_SIMP_TAC list_ss [MEM_SPLIT]

               >> ASSUME_TAC (INST_TYPE [alpha |-> ``:cand``] ALL_DISTINCT_APPEND)
               >> first_assum (qspecl_then [`MAP FST l1`,`MAP FST ([(c,x)] ++ l2)`] strip_assume_tac)
               >> `ALL_DISTINCT ((MAP FST l1) ++ (MAP FST ([(c,x)] ++ l2)))`
	        by FULL_SIMP_TAC list_ss [ALL_DISTINCT_APPEND, MAP_APPEND]
               >> `!e. MEM e (MAP FST l1) ==> (~ MEM e (MAP FST ([(c,x)] ++ l2)))` by metis_tac[]
               >> `MEM c (MAP FST ([(c,x)] ++ l2))` by FULL_SIMP_TAC list_ss [MAP_APPEND]
               >> `~ MEM c (MAP FST l1)` by metis_tac[]
               >> ASSUME_TAC get_cand_pile_APPEND
               >> first_assum (qspecl_then [`l1`,`(c,y)::l2`] strip_assume_tac)
               >>  fs [get_cand_pile_def,get_cand_pile_APPEND,ALOOKUP_def]));






val Logical_subpile1_IMP_TheFunctional = Q.store_thm ("Logical_subpile1_IMP_TheFunctional",
 `! p1 p2 c. (!d'. ((d' <> c) ==> (!l. (MEM (d',l) p1 ==> MEM (d',l) p2)))
                /\ ((d' = c) ==> (MEM (c,[]) p2))) ==> (subpile1 c p1 p2)`,

         Induct_on `p1`
           >- rw[subpile1_def]
           >- ((REPEAT STRIP_TAC
             >>  rw[subpile1_def])
               >-( Cases_on `c = FST h`
                   >- RW_TAC bool_ss []
                   >- (first_assum (qspecl_then [`FST h`] strip_assume_tac)
		       >> fs[]))
          >- rfs[subpile1_def]

          >- (first_assum (qspecl_then [`FST h`] strip_assume_tac)
            >> rfs[]
            >> ` (FST h,SND h) = h` by rfs[PAIR]
             >> `MEM (FST h, SND h) p2` by metis_tac[PAIR,PAIR_EQ]
               >> fs[])

           >- rfs[subpile1_def]));



val SUBPILE_TWO_HEAD_REMOVAL = Q.store_thm ("SUBPILE_TWO_HEAD_REMOVAL",
 `!p1 p2 c h. (subpile2 c (h::p2) p1) ==> (subpile2 c p2 p1) `,
 rw[subpile2_def]);


val Functional_subpile2_IMP_TheLogical = Q.store_thm ("Functional_subpile2_IMP_TheLogical",
 `!p1 p2 c. (subpile2 c p2 p1) ==>  (!d'. ((d' <> c) ==> (!l. (MEM (d',l) p2 ==> MEM (d',l) p1))))`,

    Induct_on `p2`
        >- rw []
        >- ((REPEAT STRIP_TAC
          >> FULL_SIMP_TAC bool_ss [MEM])
             >- (`d' = FST h` by RW_TAC bool_ss [PAIR_EQ,FST]
               >> `c <> FST h` by RW_TAC bool_ss []
                 >>  RW_TAC bool_ss [subpile2_def]
                   >> FULL_SIMP_TAC list_ss [subpile2_def])
             >- (first_assum (qspecl_then [`p1`,`c`] strip_assume_tac)
               >> metis_tac [SUBPILE_TWO_HEAD_REMOVAL])));


val subpile1_CandPile_Empty = Q.store_thm ("subpile1_CandPile_Empty",
 `!(l: cand list) p1 p2 c. (subpile1 c p1 p2) /\ (MEM c (MAP FST p2))
                                              /\ (MEM c (MAP FST p1))  ==> (MEM (c,[]) p2)`,

Induct_on `p1`
     >- rw[]
   >- ((REPEAT STRIP_TAC
          >> Cases_on `c = FST h`)
          >- (FULL_SIMP_TAC list_ss [subpile1_def]
              >> metis_tac [subpile1_def,MAP,MEM])
         >- fs[subpile1_def,MEM]));




val Logical_subpile2_IMP_TheFunctional = Q.store_thm ("Logical_subpile2_IMP_TheFunctional",
 `!p1 p2 c. (!d'. ((d' <> c) ==> (!l. (MEM (d',l) p2 ==> MEM (d',l) p1)))
              /\ ((d' = c) ==> (?l. MEM (c,l) p1))) ==> (subpile2 c p2 p1)`,

      Induct_on `p2`
           >-   rw[subpile2_def]
           >- ((REPEAT STRIP_TAC
	       >> Cases_on `c = FST h`)
                 >-  fs [subpile2_def]
                 >- (fs [subpile2_def]
                     >> first_assum(qspecl_then [`FST h`] strip_assume_tac)
                       >> rfs[]
                        >> `MEM (FST h,SND h) p1` by rfs[PAIR,PAIR_EQ]
                          >> metis_tac[PAIR,PAIR_EQ])));



val logical_GetCandPile_IMP_TheFunctional = Q.store_thm ("logical_GetCandPile_IMP_TheFunctional",
 `!(p: (cand # (((cand list) # rat) list)) list) nba c. (!d. (d <> c) ==>
   (!l. MEM (d,l) p ==> ~ ((d,l) = (d,nba)))) /\ (!d. (d = c) ==> (!l. MEM (c,l) p /\ ((c,l) = (c,nba))))
/\ MEM c (MAP FST p) ==> (nba = get_cand_pile c p)`,

    Induct_on `p`
        >- rw[]
        >- ((REPEAT STRIP_TAC >>
	     Cases_on `c = FSt h`)
               >- (ASSUME_TAC GET_CAND_PILE_MEM
                 >> first_assum (qspecl_then [`h::p`,`c`] strip_assume_tac)
                   >> `MEM (c,get_cand_pile c (h::p)) (h::p)` by metis_tac[]
                     >> `(c,get_cand_pile c (h::p)) =  (c,nba)` by metis_tac[]
                       >> RW_TAC bool_ss [PAIR_EQ,EQ_SYM_EQ])
            >- metis_tac[MEM,MAP,PAIR_EQ,EQ_SYM_EQ]));



val list_not_MEM_verified_fully= Q.store_thm ("list_not_MEM_verified_fully",
 `!l1 (l2: cand list). (!c. MEM c l1 ==> (~ MEM c l2)) <=> (list_not_MEM l1 l2)`,



        Induct_on `l1`
             >- rw[]
             >- (REPEAT STRIP_TAC
	          >> fs[]
                    >> metis_tac[MEM]));


val Logical_list_MEM_VICE_VERCA_TheFunctional = Q.store_thm("Logical_list_MEM_VICE_VERCA_TheFunctional",
 `!(l1: cand list) l2. (!c. MEM c l1 ==> MEM c l2) <=> list_MEM l1 l2`,

    Induct_on `l1`
      >- fs[]
      >- (REPEAT STRIP_TAC >> fs[]
        >> metis_tac[MEM]));

val Valid_PileTally_thm = Q.store_thm("Valid_PileTally_thm",
  `∀x y. Valid_PileTally x y ⇔ Valid_PileTally_dec1 x y ∧ Valid_PileTally_dec2 x y`,
  simp[Valid_PileTally_def,EQ_IMP_THM]
  \\ metis_tac[
       PileTally_to_PileTally_DEC1,PileTally_DEC1_to_PileTally,
       PileTally_to_PileTally_DEC2,PileTally_DEC2_IMP_PileTally]);

(*
val ELIM_CAND_thm = Q.store_thm("ELIM_CAND_thm",
  `ELIM_CAND_dec = ELIM_CAND`,
  simp[FUN_EQ_THM]
  \\ qx_genl_tac[`c`,`p`,`j1`,`j2`]
  \\ PairCases_on`p`
  \\ map_every qid_spec_tac [`j2`,`j1`,`p2`,`p1`,`p0`,`c`]
  \\ recInduct ELIM_CAND_dec_ind
  \\ rw[ELIM_CAND_def,ELIM_CAND_dec_def,Valid_PileTally_thm,
        list_MEM_dec_thm,Valid_Init_CandList_def,NULL_EQ,
        SUBSET_DEF]
  \\ rw[EQ_IMP_THM]
  \\ imp_res_tac Valid_PileTally_thm
  \\ fs[Valid_PileTally_def]
*)

(*
val Elim_cand_dec_def = Define `
             (Elim_cand_dec st (qu : rat) (l: cand list) (c:cand) ((j: judgement), winners w) = F)
          /\ (Elim_cand_dec st qu l c (winners w, (j: judgement)) = F)
          /\ (Elim_cand_dec st qu l c (state (ba, t, p, bl, e, h), state (ba', t', p', bl', e',h')) =
                  ((NULL ba)
               /\ (NULL bl)
               /\ (t = t') /\ (bl = bl') /\ (e = e')
               /\ (LENGTH (e ++ h) > st) /\ (LENGTH e < st)
               /\ (~ (NULL l) /\ (ALL_DISTINCT l)
               /\ (list_MEM (h++e) l)
               /\ (ALL_DISTINCT (h++e))
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
*)

(* to be reconstructed

val Logical_elim_to_Functional_Elim = Q.store_thm ("Logical_elim_to_Functional_Elim",
 `!st qu l c j1 j2. ELIM_CAND c (qu,st,l) j1 j2 ==> (ELIM_CAND_dec c (qu,st,l) j1 j2)`,

   (rw[ELIM_CAND_def,ELIM_CAND_dec_def]
    >> EVAL_TAC
     >> REPEAT STRIP_TAC)
      >- rw[]
      >- RW_TAC bool_ss []
      >- (`l <> []` by metis_tac[Valid_Init_CandList_def]
         >> `?l1 x. l = x::l1` by metis_tac [list_nchotomy]
           >> fs[NULL])
      >- fs[Valid_Init_CandList_def]
      >- (`!(l1:cand list) l2 (c':cand). MEM c' l1 \/ MEM c' l2 ==> MEM c' (l1++l2)`
              by FULL_SIMP_TAC list_ss [MEM,MEM_APPEND]
          >> `!c'. MEM c' (h++e) ==> MEM c' l` by metis_tac [MEM,MEM_APPEND]
            >> metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional])
      >- rw[]
      >- metis_tac [PileTally_to_PileTally_DEC1,Valid_PileTally_def]
      >- metis_tac [PileTally_to_PileTally_DEC2,Valid_PileTally_def]
      >- metis_tac [PileTally_to_PileTally_DEC1,Valid_PileTally_def]
      >- metis_tac [PileTally_to_PileTally_DEC2,Valid_PileTally_def]
      >- rw []
      >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1]
      >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC2]
      >- rw []


      >- metis_tac [LogicalLessThanQu_IMP_less_than_quota,Valid_PileTally_def,ALOOKUP_def]
      >- metis_tac [EQE_IMP_REMOVE_ONE_CAND]
      >- (`MEM c (MAP FST t)` by metis_tac [Valid_PileTally,FST,MAP]
        >> `!d. MEM d h ==> MEM d (MAP FST t)` by metis_tac [Valid_PileTally]
         >> metis_tac [Logical_bigger_than_cand_IMP_TheFunctional])
      >- rw[]
      >- metis_tac [Logical_subpile1_IMP_TheFunctional]
      >- (`!d. (d = c) ==> ?l. MEM (c,l) p` by metis_tac[GET_CAND_PILE_MEM,Valid_PileTally]
          >> metis_tac [Logical_subpile2_IMP_TheFunctional]));
*)


(* to be reconstructed

val Functional_Elim_to_Logical_elim = Q.store_thm ("Functional_Elim_to_Logical_elim",
 `!st qu l c j1 j2. ELIM_CAND_dec c (qu,st,l) j1 j2 ==> ELIM_CAND c (qu,st,l) j1 j2`,



  (STRIP_TAC
     >> STRIP_TAC >> STRIP_TAC >> STRIP_TAC >> STRIP_TAC >> STRIP_TAC
       >> Cases_on `j1`)
         >- (Cases_on `j2`
           >- ((rw[ELIM_CAND_dec_def,ELIM_CAND_def]
            >> Cases_on `p` >> Cases_on `r` >> Cases_on `r'` >> Cases_on `r` >> Cases_on `r'`
             >> Cases_on `p'` >> Cases_on `r'` >> Cases_on `r''` >> Cases_on `r'` >> Cases_on `r''`
              >>  rfs[ELIM_CAND_def,ELIM_CAND_dec_def]
               >> REPEAT STRIP_TAC)
                >- metis_tac[empty_list_verified]
                >- (RW_TAC bool_ss [empty_list_def]
                 >> metis_tac [empty_list_verified])
                >- (`!(L:Cand list). non_empty L ==> (L <> [])`
                  by (Induct_on `L`
                     >- rw[non_empty]
                     >- rw[non_empty]) >> metis_tac[Valid_Init_CandList,no_dup_IMP_NO_DUP_PRED,non_empty])
                >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND]
                >- (RW_TAC bool_ss [] >> metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND])
                >- (RW_TAC bool_ss [] >> metis_tac [no_dup_IMP_NO_DUP_PRED])
                >- metis_tac [Valid_PileTally,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
                >- metis_tac [Valid_PileTally,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
                >- metis_tac[]
                >- metis_tac[]
                >- metis_tac [no_dup_IMP_NO_DUP_PRED]
                >- metis_tac [Valid_PileTally,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
                >- (`!(L:Cand list). non_empty L ==> (L <> [])`
                   by (Induct_on `L`
                     >- rw[non_empty]
                     >- rw[non_empty]) >> `?L y. l = y::L` by metis_tac[non_empty,list_nchotomy]
                      >> `MEM y (MAP FST q')` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM]
                      >> `?l1 q1. q' = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy]
                      >> `!d. MEM d r ==> MEM d l`
                           by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
                      >> `!d. MEM d r ==> MEM d (MAP FST q')` by metis_tac [PileTally_DEC2_IMP_PileTally]
                    >> metis_tac[PileTally_to_PileTally_DEC2,less_than_qu_IMP_LogicalLessThanQuota])
                >- (`!(L:Cand list). non_empty L ==> (L <> [])`
                   by (Induct_on `L`
                    >- rw[non_empty]
                    >- rw[non_empty]) >> `?L y. l = y::L` by metis_tac[non_empty,list_nchotomy]
                     >> `MEM y (MAP FST q')` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM]
                     >> `?l1 q1. q' = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy]
                     >> `!d. MEM d r ==> MEM d l`
                         by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
                     >> `!d. MEM d r ==> MEM d (MAP FST q')` by metis_tac [PileTally_DEC2_IMP_PileTally]
                     >> metis_tac [PileTally_to_PileTally_DEC2,bigger_than_cand_LogicallyOK])
                >- (`!(l1 :Cand list) l2. no_dup (l1++l2) ==> no_dup l1`
                    by (Induct_on `l1`
                     >- rw[no_dup]
                     >- ((REPEAT STRIP_TAC >> rw[no_dup])
                        >- (`not_elem h (l1++l2)` by rfs [no_dup]
                         >>`!G1 G2 (s: Cand). (not_elem s (G1++G2) = (not_elem s G1) /\ (not_elem s G2))`
                             by (Induct_on `G1`
                              >- FULL_SIMP_TAC list_ss [APPEND_NIL_LEFT,not_elem]
                              >- ((ASSUME_TAC CAND_EQ_DEC >> REPEAT STRIP_TAC
                                >> first_x_assum (qspecl_then [`s`,`h'`] strip_assume_tac))
                                 >- FULL_SIMP_TAC list_ss [not_elem]
                                 >- FULL_SIMP_TAC list_ss [not_elem])) >> metis_tac[])
                        >- (`!d. NO_DUP_PRED (h::l1++l2) d` by metis_tac [no_dup_IMP_NO_DUP_PRED]
                          >> `h::l1++l2 = h::(l1++l2)` by FULL_SIMP_TAC list_ss []
                           >> `!d. NO_DUP_PRED (l1++l2) d` by metis_tac [NO_DUP_HEAD_REMOVAL]
                            >> metis_tac [NO_DUP_PRED_to_no_dup])))
                    >> metis_tac [EQE_REMOVE_ONE_CAND,no_dup_IMP_NO_DUP_PRED])
                >- metis_tac [Functional_subpile1_IMP_TheLogical]
                >- metis_tac [Functional_subpile2_IMP_TheLogical]
                >- metis_tac [empty_list_verified])

            >- rw[Elim_cand_dec_def])
        >- (Cases_on `j2`
            >- RW_TAC bool_ss [Elim_cand_dec_def]
            >- rw[Elim_cand_dec_def]));
*)


(* to be reconstructed

val Logical_transfer_to_Functional_Transfer = Q.store_thm ("Logical_transfer_to_Functional_Transfer",
 `! st qu l j1 j2. TRANSFER (qu,st,l) j1 j2 ==> TRANSFER_dec (qu,st,l) j1 j2`,

(rw[TRANSFER_def,TRANSFER_dec_def]
  >> EVAL_TAC
    >> REPEAT STRIP_TAC)

     >- rw[]
     >- (`(!d. MEM d h \/ MEM d e ==> MEM d l) ==> (!d. MEM d (h++e) ==> MEM d l)`
         by  FULL_SIMP_TAC list_ss [MEM_APPEND] >>
      metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional])
     >- rw[]
     >- metis_tac [PileTally_to_PileTally_DEC1,Valid_PileTally_def]
     >- metis_tac [PileTally_to_PileTally_DEC2,Valid_PileTally_def]
     >- metis_tac [PileTally_to_PileTally_DEC1,Valid_PileTally_def]
     >- metis_tac [PileTally_to_PileTally_DEC2,Valid_PileTally_def]
     >- metis_tac [PileTally_to_PileTally_DEC1,Valid_PileTally_def]
     >- metis_tac [PileTally_to_PileTally_DEC2,Valid_PileTally_def]
     >- (`?l1 y. l = y::l1` by metis_tac [Valid_Init_CandList_def,list_nchotomy]
         >> fs[NULL])
     >- metis_tac [Valid_Init_CandList_def]
     >- rw[]
     >- metis_tac [LogicalLessThanQu_IMP_less_than_quota,Valid_PileTally_def]
     >- RW_TAC bool_ss []
     >- metis_tac [Logical_subpile1_IMP_TheFunctional]
     >- (`?(y: (Cand # (((Cand list) # rat) list))). (c = FST y) /\ (MEM y np)`
        by (MAP_EVERY qexists_tac [`(c,[])`] >> metis_tac [FST])
        >> `MEM c (MAP FST np)` by metis_tac[MEM_MAP]
          >> `!d. (d = c) ==> ?l. MEM (c,l) p` by metis_tac[GET_CAND_PILE_MEM,Valid_PileTally]
           >> metis_tac [Logical_subpile2_IMP_TheFunctional]));



val Functional_Transfer_to_Logical_transfer = Q.store_thm ("Functional_Transfer_to_Logical_transfer",
 `! st qu l j1 j2. Transfer_dec st qu l (j1,j2) ==> transfer st qu l j1 j2`,

 (REPEAT STRIP_TAC
  >> rw[transfer_def]
    >> Cases_on `j1`)
      >- (Cases_on `j2`
        >- ((Cases_on `p` >> Cases_on `r` >> Cases_on `r'` >> Cases_on `r` >> Cases_on `r'`
          >> Cases_on `p'` >> Cases_on `r'`>> Cases_on `r''`>> Cases_on `r'`>> Cases_on `r''`
           >> rfs [Transfer_dec_def]
            >> MAP_EVERY qexists_tac [`q'''''`,`TL q'''`,`q'''''''`] >> REPEAT STRIP_TAC)
       >- rw[empty_list_verified]
       >-  RW_TAC bool_ss []
       >-  metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
       >-  metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
       >-  metis_tac [no_dup_IMP_NO_DUP_PRED]
       >-  metis_tac [Valid_PileTally,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
       >-  metis_tac [Valid_PileTally,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
       >-  metis_tac [Valid_PileTally,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
       >- (`!(L:Cand list). non_empty L ==> (L <> [])`
                  by (Induct_on `L`
                     >- rw[non_empty]
                     >- rw[non_empty])
           >> metis_tac[Valid_Init_CandList,no_dup_IMP_NO_DUP_PRED,non_empty])
       >- metis_tac [no_dup_IMP_NO_DUP_PRED]
       >- (`!(L:Cand list). non_empty L ==> (L <> [])`
                   by (Induct_on `L`
                     >- rw[non_empty]
                     >- rw[non_empty]) >> `?L y. l = y::L` by metis_tac[non_empty,list_nchotomy]
                      >> `MEM y (MAP FST q')` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM]
                      >> `?l1 q1. q' = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy]
                      >> `!d. MEM d r ==> MEM d l`
                           by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
                      >> `!d. MEM d r ==> MEM d (MAP FST q')` by metis_tac [PileTally_DEC2_IMP_PileTally]
                    >> metis_tac[PileTally_to_PileTally_DEC2,less_than_qu_IMP_LogicalLessThanQuota])
       >- ((MAP_EVERY qexists_tac [`HD q'''`] >> REPEAT STRIP_TAC)
         >- FULL_SIMP_TAC list_ss []
         >- rw[]
         >- RW_TAC bool_ss []
         >- metis_tac [Functional_subpile1_IMP_TheLogical]
         >- metis_tac [Functional_subpile2_IMP_TheLogical]
         >- rw[]
         >- EVAL_TAC
         >- rw[]))
     >- rfs [Transfer_dec_def])
    >- (Cases_on `j2`
     >- rfs [Transfer_dec_def]
     >- rfs [Transfer_dec_def]));
*)



val fcc_to_first_continuing_cand = Q.store_thm ("fcc_to_first_continuing_cand",
 `! c b h. first_continuing_cand_dec c b h ==> first_continuing_cand c b h`,

  Induct_on `b`
    >- rw[first_continuing_cand_dec_def]
    >- ((REPEAT STRIP_TAC
      >>  rw[first_continuing_cand_def]
       >> Cases_on `c = h`)
         >- (MAP_EVERY qexists_tac [`[]`,`b`]
          >> FULL_SIMP_TAC list_ss [APPEND_NIL_LEFT])
         >- (rfs [first_continuing_cand_dec_def]
           >- RW_TAC bool_ss []
           >- (rfs [first_continuing_cand_def]
            >> `?L1 L2. (b = L1 ++ [c]++L2) /\ (!d. MEM d L1 ==> ~ MEM d h')` by metis_tac[]
             >> MAP_EVERY qexists_tac [`h::L1`,`L2`]
              >> FULL_SIMP_TAC list_ss [MEM] >> metis_tac [MEM]))));



val first_continuing_cand_IMP_fcc = Q.store_thm ("first_continuing_cand_IMP_fcc",
 `! c b h. first_continuing_cand c b h ==> first_continuing_cand_dec c b h`,

Induct_on `b`

>- rw[first_continuing_cand_def]

>- ((REPEAT STRIP_TAC
  >> rw[first_continuing_cand_dec_def]
    >> Cases_on `c = h`)

    >- RW_TAC bool_ss []

    >- ((rfs [first_continuing_cand_def]
      >> `(l1 = []) \/ (?L1 x. l1 = x::L1)` by metis_tac [list_nchotomy])

        >- FULL_SIMP_TAC list_ss [APPEND_NIL_LEFT,CONS_11]

        >- (FULL_SIMP_TAC list_ss [CONS_11]
          >> first_assum (qspecl_then [`c`,`h'`] strip_assume_tac)
            >> metis_tac [MEM]))));



val intermediate_count_def = Define `
        (intermediate_count (qu,st,l) j1 j2 = ? ba t nt p np bl e h.
          (j1 = NonFinal (ba, t, p, bl, e, h))
       /\ (!d. MEM d (h++e) ==> MEM d l)
       /\ ALL_DISTINCT (h++e)
       /\ (Valid_PileTally t l)
       /\ (Valid_PileTally nt l)
       /\ (Valid_PileTally p l)
       /\ (Valid_PileTally np l)
       /\ (Valid_Init_CandList l)
       /\ ALL_DISTINCT (MAP FST p)
       /\ ALL_DISTINCT (MAP FST t)
       /\ ALL_DISTINCT (MAP FST np)
       /\ ALL_DISTINCT (MAP FST nt)
       /\ (ba <> [])
       /\ (h <> [])
       /\ (!c. MEM c l ==>
                            ((MEM c h ==>
                             ?(l: ((cand list) # rat) list).
                               (l = FILTER (\ (b: (cand list) # rat). (first_continuing_cand c (FST b) h)) ba)
                            /\ (get_cand_pile c np = (get_cand_pile c p) ++ l)
                            /\ (get_cand_tally c nt = (SUM_RAT (MAP SND l))))
                            /\ (~ MEM c h ==>
                                           (get_cand_pile c np = get_cand_pile c p)
                                        /\ (get_cand_tally c nt = get_cand_tally c t))))
       /\ (j2 = NonFinal ([], nt, np, bl, e, h)))`;


val COUNTAux_dec = Define `
     (COUNTAux_dec p np t t' ba h ([]: cand list) = T)
  /\ (COUNTAux_dec p np t t' ba  (h: cand list) (l0::ls) =
       if (MEM l0 h) then
        (get_cand_pile l0 np = (get_cand_pile l0 p) ++ FILTER (\ (b: (cand list) # rat). (first_continuing_cand_dec l0 (FST b) h)) ba)
          /\ ((get_cand_tally l0 t') = SUM_RAT (MAP SND (FILTER (\ (b: (cand list) # rat). (first_continuing_cand_dec l0 (FST b) h)) ba)))
           /\ (COUNTAux_dec p np t t' ba h ls)
        else
             (get_cand_pile l0 np = get_cand_pile l0 p)
          /\ ((get_cand_tally l0 t') = get_cand_tally l0 t)
          /\ (COUNTAux_dec p np t t' ba h ls))`;


val Logical_to_Functional_Count_Dec_Aux = Q.store_thm ("Logical_to_Functional_Count_Dec_Aux",
 `!t nt p np ba h l.
          (!c. MEM c l ==>
                 ((MEM c h ==>
                    ?(l: ((cand list) # rat) list).
                      (l = FILTER (\ (b: (cand list) # rat). (first_continuing_cand c (FST b) h)) ba)
                         /\ (get_cand_pile c np = (get_cand_pile c p) ++ l)
                         /\ (get_cand_tally c nt = (SUM_RAT (MAP SND l))))
                         /\ (~ MEM c h ==>
                                      (get_cand_pile c np = get_cand_pile c p)
                                      /\ (get_cand_tally c nt = get_cand_tally c t))))
                                           ==> COUNTAux_dec p np t nt ba h l`,


Induct_on `l`
  >- rw[COUNTAux_dec]
  >- ((REPEAT STRIP_TAC
      >> rw[COUNTAux_dec])

    >- (first_assum (qspecl_then [`h`] strip_assume_tac)
     >> FULL_SIMP_TAC list_ss [MEM]
      >> `!c h ba. first_continuing_cand c h ba <=> first_continuing_cand_dec c h ba`
              by metis_tac [first_continuing_cand_IMP_fcc,fcc_to_first_continuing_cand]
         >> metis_tac [])

    >- (first_assum (qspecl_then [`h`] strip_assume_tac)
     >> FULL_SIMP_TAC list_ss []
       >> `!c h ba. first_continuing_cand c h ba <=> first_continuing_cand_dec c h ba`
              by metis_tac [first_continuing_cand_IMP_fcc,fcc_to_first_continuing_cand]
         >> metis_tac [])));




val Functional_to_Logical_Count_Dec_Aux = Q.store_thm ("Functional_to_Logical_Count_Dec_Aux",
`!t nt p np ba h l. COUNTAux_dec p np t nt ba h l ==>
          (!c. MEM c l ==>
                 ((MEM c h ==>
                    ?(l: ((cand list) # rat) list).
                      (l = FILTER (\ (b: (cand list) # rat). (first_continuing_cand c (FST b) h)) ba)
                         /\ (get_cand_pile c np = (get_cand_pile c p) ++ l)
                         /\ (get_cand_tally c nt = (SUM_RAT (MAP SND l))))
                         /\ (~ MEM c h ==>
                                      (get_cand_pile c np = get_cand_pile c p)
                                      /\ (get_cand_tally c nt = get_cand_tally c t))))`,


Induct_on `l`
  >- rw[]
  >- (REPEAT STRIP_TAC
      >- (`(c = h) \/ (MEM c l)` by FULL_SIMP_TAC list_ss [MEM]
           >- ((MAP_EVERY qexists_tac [`FILTER (\ (b: (cand list) # rat). (first_continuing_cand_dec c (FST b) h')) ba`]
            >> `!c h ba. first_continuing_cand c h ba <=> first_continuing_cand_dec c h ba`
              by metis_tac [first_continuing_cand_IMP_fcc,fcc_to_first_continuing_cand]
              >>  STRIP_TAC)
                 >- metis_tac []
                 >- metis_tac[COUNTAux_dec])
           >- ((MAP_EVERY qexists_tac [`FILTER (\ (b: (cand list) # rat). (first_continuing_cand_dec c (FST b) h')) ba`]
            >> `!c h ba. first_continuing_cand c h ba <=> first_continuing_cand_dec c h ba`
              by metis_tac [first_continuing_cand_IMP_fcc,fcc_to_first_continuing_cand]
              >> STRIP_TAC)
                >- metis_tac []
                >- metis_tac [COUNTAux_dec]))
       >- metis_tac[COUNTAux_dec,MEM]
       >- metis_tac [COUNTAux_dec,MEM]));



val intermediate_count_IMP_Count_Aux = Q.store_thm ("intermediate_count_IMP_Count_Aux",
 `! (st: num) (qu: rat) l j1 j2. intermediate_count (qu,st,l) j1 j2 ==> COUNT (qu,st,l) j1 j2`,


(REPEAT STRIP_TAC >> rw[COUNT_def] >> rfs[intermediate_count_def]
     >> STRIP_TAC)
     >- metis_tac[]
     >- (REPEAT STRIP_TAC

       >- metis_tac[Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_PILE]
       >- (`!L. MEM (c,L) nt' ==> (get_cand_tally c nt' = L)` by
            metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_TALLY]
         >> `!L. MEM (c,L) t ==> (get_cand_tally c t = L)` by
           metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_TALLY]
	    >> metis_tac[])
       >- (`!L. MEM (c,L) np ==> (get_cand_pile c np = L)` by
            metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_PILE]
         >> `!L. MEM (c,L) p ==> (get_cand_pile c p = L)` by
            metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_PILE]
         >> `!L. MEM (c,L) p ==> MEM (c,L) np` by (REPEAT STRIP_TAC >>
              metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,GET_CAND_PILE_MEM])
            >> `!L. MEM (c,L) np ==> MEM (c,L) p` by (REPEAT STRIP_TAC >>
                 metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,GET_CAND_PILE_MEM])
              >> metis_tac [])
        >- (`!L. MEM (c,L) nt' ==> (get_cand_tally c nt' = L)` by
            metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_TALLY]
         >> `!L. MEM (c,L) t ==> (get_cand_tally c t = L)` by
           metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_TALLY]
         >> `!L. MEM (c,L) t ==> MEM (c,L) nt'` by (REPEAT STRIP_TAC >>
              metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,GET_CAND_TALLY_MEM2])
            >> `!L. MEM (c,L) nt' ==> MEM (c,L) t` by (REPEAT STRIP_TAC >>
                 metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,GET_CAND_TALLY_MEM2])
              >> metis_tac [])));




val Count_Aux_IMP_intermediate_count = Q.store_thm ("Count_Aux_IMP_intermediate_count",
`! (st: num) (qu: rat) l j1 j2. COUNT (qu,st,l) j1 j2 ==> intermediate_count (qu,st,l) j1 j2`,

(REPEAT STRIP_TAC
 >> rw[intermediate_count_def]
  >> rfs[COUNT_def]
   >> STRIP_TAC)
   >- metis_tac[]
   >- (REPEAT STRIP_TAC
     >- (`(!l'. MEM (c,l') np ==>
       (l' = (get_cand_pile c p) ++ (FILTER (\ (b: (cand list) # rat).(first_continuing_cand c (FST b) h)) ba)))`
        by  metis_tac[]
      >> first_assum (qspecl_then [`get_cand_pile c np`] strip_assume_tac)
        >> metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,GET_CAND_PILE_MEM])
     >- metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,GET_CAND_TALLY_MEM2]
     >- (`(!l'. MEM c l /\ MEM (c,l') np <=> MEM c l /\ MEM (c,l') p)` by metis_tac []
       >> `MEM (c,get_cand_pile c np) p` by
           metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE]
         >> metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_PILE])
     >- (`(!r. MEM c l /\ MEM (c,r) t <=> MEM c l /\ MEM (c,r) nt') ` by metis_tac []
      >> metis_tac [Valid_PileTally_def,PileTally_DEC2_IMP_PileTally,EVERY_CAND_HAS_ONE_TALLY,GET_CAND_TALLY_MEM2])));





(* to be reconstructed

val Count_Aux_IMP_Count_Aux_dec = Q.store_thm ("Count_Aux_IMP_Count_Aux_dec",
 `! (st: num) (qu: rat) l j1 j2. COUNT (qu,st,l) j1 j2 ==> COUNT_dec (qu,st,l) j1 j2`,

  (ASSUME_TAC Count_Aux_IMP_intermediate_count
   >> REPEAT STRIP_TAC
   >> `intermediate_count (qu,st,l) j1 j2` by metis_tac[COUNT_def,Count_Aux_IMP_intermediate_count]
     >> rfs[COUNT_dec_def,COUNT_def]
      >> REPEAT STRIP_TAC)
        >-  (rfs [intermediate_count_def]
         ASSUME_TAC Logical_to_Functional_Count_Dec_Aux
        first_assum (qspecl_then [`t`,`nt'`,`p`,`np`,`ba`,`h`,`l`] strip_assume_tac)
        `!c. MEM c l ==>
	      (MEM c h ==>
	               ?l. (l = FILTER (λb. first_continuing_cand c (FST b) h) ba) /\
		       (get_cand_pile c np = (get_cand_pile c p) ++ l) /\
		       (get_cand_tally c nt' = SUM_RAT (MAP SND l)))
	  /\  ((~ MEM c h) ==>
	               (get_cand_pile c np = get_cand_pile c p) /\
		       (get_cand_tally c nt' = get_cand_tally c t))`
		       by (REPEAT STRIP_TAC
                      >- (MAP_EVERY qexists_tac [`FILTER (λb. first_continuing_cand c (FST b) h) ba`]
		        >> fs[])
                      >- metis_tac[]
                      >- metis_tac[])
         metis_tac simp_tac bool_ss fs[COUNTAux_dec_def, Logical_to_Functional_Count_Dec_Aux] 		         UNDISCH_TAC [`!c. MEM c l ==>
	      (MEM c h ==>
	               ?l. (l = FILTER (λb. first_continuing_cand c (FST b) h) ba) /\
		       (get_cand_pile c np = (get_cand_pile c p) ++ l) /\
		       (get_cand_tally c nt' = SUM_RAT (MAP SND l)))
	  /\  ((~ MEM c h) ==>
	               (get_cand_pile c np = get_cand_pile c p) /\
		       (get_cand_tally c nt' = get_cand_tally c t))`]



>- metis_tac[]
        >- metis_tac[]
        >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND]
        >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1]
        >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC2]
        >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1]
        >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC2]
        >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1]
        >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC2]
        >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1]
        >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC2]
        >- metis_tac []
        >- metis_tac []
        >- (`l <> []` by metis_tac[Valid_Init_CandList_def]
         >> `?l1 x. l = x::l1` by metis_tac [list_nchotomy]
           >> fs[NULL])
        >- metis_tac [Valid_Init_CandList_def]
        >- metis_tac []
        >- (`? X BA. ba = X::BA` by metis_tac [list_nchotomy] >> fs[NULL])
        >- (`? h0 hs. h = h0::hs` by metis_tac [list_nchotomy] >> fs[NULL]));
*)

(* to be reconstructed

val Count_Aux_dec_IMP_Count_Aux = Q.store_thm ("Count_Aux_dec_IMP_Count_Aux",
 `! (st : num) (qu:rat) l j1 j2. COUNT_dec (qu,st,l) j1 j2 ==> COUNT (qu,st,l) j1 j2 `,

 (ASSUME_TAC intermediate_count_IMP_Count_Aux
  >> REPEAT STRIP_TAC
    >> `intermediate_count (qu,st,l) j1 j2` by
      (Cases_on `j1`
       >- (Cases_on `j2`
         >- ((Cases_on `p` >> Cases_on `r` >> Cases_on `r'` >> Cases_on `r` >> Cases_on `r'`
           >> Cases_on `p'` >> Cases_on `r'` >> Cases_on `r''` >> Cases_on `r'` >> Cases_on `r''`
             >> rfs[intermediate_count_def,Count_dec]
              >> REPEAT STRIP_TAC)
            >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND]
            >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND]
            >- metis_tac [no_dup_IMP_NO_DUP_PRED]
            >- metis_tac [Valid_PileTally,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
            >- metis_tac [Valid_PileTally,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
            >- metis_tac [Valid_PileTally,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
            >- metis_tac [Valid_PileTally,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
            >- (`!(L:Cand list). non_empty L ==> (L <> [])`
                  by (Induct_on `L`
                     >- rw[non_empty]
                     >- rw[non_empty]) >> metis_tac[Valid_Init_CandList,no_dup_IMP_NO_DUP_PRED,non_empty])
            >- metis_tac [no_dup_IMP_NO_DUP_PRED]
            >- metis_tac [no_dup_IMP_NO_DUP_PRED]
            >- metis_tac [no_dup_IMP_NO_DUP_PRED]
            >- metis_tac [no_dup_IMP_NO_DUP_PRED]
            >- metis_tac [non_empty]
            >- metis_tac [non_empty]
            >- metis_tac [Functional_to_Logical_Count_Dec_Aux]
            >-  metis_tac [Functional_to_Logical_Count_Dec_Aux]
            >- metis_tac [Functional_to_Logical_Count_Dec_Aux]
            >- metis_tac [Functional_to_Logical_Count_Dec_Aux])
         >- rfs [COUNT_dec])
        >- (Cases_on `j2`
         >- rfs [COUNT_dec]
         >- rfs [COUNT_dec]))
           >> metis_tac[]);
*)


val APPEND_EQ_NIL2 = Q.store_thm ("APPEND_EQ_NIL2",
    `!l1 l2. ([] = l1 ++ l2) ==> ((l1 = []) /\ (l2 = [])) `,
      Cases_on `l2`
        >- ASM_SIMP_TAC bool_ss [APPEND_NIL]
        >- (Cases_on `l1`
          >> rw[APPEND_NIL_LEFT_COR]
            >> (ASM_SIMP_TAC bool_ss [NOT_NIL_CONS]
              >> STRIP_TAC
                >> rw[NOT_NIL_CONS]))) ;


val take_append_returns_appended = Q.store_thm ("take_append_returns_appended",
 `! l1 l2 l3. (l1 = l2 ++ l3) ==> (l3 = take_append l1 l2)`,

 Induct_on `l1`
  >- FULL_SIMP_TAC list_ss [APPEND_EQ_NIL2,take_append_def]
  >- (Induct_on `l2`
    >- FULL_SIMP_TAC list_ss [APPEND_NIL_LEFT,take_append_def]
    >- (REPEAT STRIP_TAC
     >> rw[take_append_def]
       >> FULL_SIMP_TAC list_ss [CONS_11])));


val eqe_list_dec_MEM1 = Q.store_thm ("list_eqe_dec_MEM1",
 `!l0 l1 l2. eqe_list_dec l0 l1 l2 ==> (!c. MEM c l0 \/ MEM c l1 ==> MEM c l2)`,

Induct_on `l0`
  >- fs [eqe_list_dec_def,Logical_list_MEM_VICE_VERCA_TheFunctional,list_MEM_dec_thm]
  >- (REPEAT STRIP_TAC
     >- metis_tac [eqe_list_dec_def,MEM]
     >- metis_tac [MEM,eqe_list_dec_def]));


val logical_to_functional_eqe_list_dec = Q.store_thm ("logical_to_functional_eqe_list_dec",
`!l0 l1 l2. (ALL_DISTINCT (l0 ++ l1)) /\ (!c. MEM c l0 \/ MEM c l1 ==> MEM c l2) ==> eqe_list_dec l0 l1 l2`,

   Induct_on `l0`
     >- metis_tac [eqe_list_dec_def,Logical_list_MEM_VICE_VERCA_TheFunctional,list_MEM_dec_thm]
     >-  ((REPEAT STRIP_TAC
       >> rw[eqe_list_dec_def])
          >- fs [ALL_DISTINCT]
          >- (`!c. MEM c l0 \/ MEM c l1 ==> MEM c l2` by metis_tac[MEM]
	    >> `ALL_DISTINCT (l0 ++ l1)` by fs[ALL_DISTINCT]
              >> metis_tac[ALL_DISTINCT,MEM])));


val eqe_list_dec2_verified = Q.store_thm ("eqe_list_dec2_verified",
 `! l0 l1 l2. eqe_list_dec2 l0 l1 l2 <=> (!c. MEM c l2 ==> MEM c l0 \/ MEM c l1)`,
  Induct_on `l2`
    >-  (EVAL_TAC >> rw[])
    >- (REPEAT STRIP_TAC >> rfs[]
        >> fs[eqe_list_dec2_def]
        >> metis_tac[eqe_list_dec2_def]));

val functional_to_logical_BiggerThanQuota = Q.store_thm ("logical_to_functional_BiggerThanQuota",
 `! (qu:rat) l t. bigger_than_quota l t qu /\ ALL_DISTINCT (MAP FST t) ==>
                                     (!c. MEM c l ==> (!r. MEM (c,r) t ==> qu <= r))`,

  Induct_on `l`
    >- rw[]
    >- ((REPEAT STRIP_TAC
      >> FULL_SIMP_TAC list_ss [])
         >- (`get_cand_tally c t = r` by metis_tac [ALL_DISTINCT,EVERY_CAND_HAS_ONE_TALLY]
           >> RW_TAC bool_ss [] >> rfs[bigger_than_quota_def])
         >- (`bigger_than_quota l t qu` by fs[bigger_than_quota_def]
	    >> metis_tac [])));



val logical_to_functional_BiggerThanQuota = Q.store_thm ("logical_to_functional_BiggerThanQuota",
`! (qu: rat) l t. (ALL_DISTINCT (MAP FST t)) /\ (!d. MEM d l ==> MEM d (MAP FST t)) /\
                  (!c. MEM c l ==> (!r. MEM (c,r) t ==> qu <= r)) ==> bigger_than_quota l t qu`,

  Induct_on `l`
     >- rw[bigger_than_quota_def]
     >- ((REPEAT STRIP_TAC
       >> rw[bigger_than_quota_def])
          >- (`MEM (h,get_cand_tally h t) t` by metis_tac [MEM,GET_CAND_TALLY_MEM2]
            >> metis_tac[MEM])
          >- metis_tac [bigger_than_quota_def,MEM]));


val functional_to_logicl_piles_eq = Q.store_thm ("functional_to_logical_piles_eq",
 `! l1 l2 p1 p2. ALL_DISTINCT (MAP FST p1) /\ ALL_DISTINCT (MAP FST p2) /\ (list_MEM l1 (MAP FST p1)) /\
                (list_MEM l1 (MAP FST p2)) /\ (piles_eq_list l1 l2 p1 p2) ==>
   (!c. MEM c l1 ==> (~ MEM c l2 ==> (!l'. MEM (c,l') p1 <=> MEM (c,l') p2)))`,

Induct_on `l1`
 >- rw[]

 >- ((REPEAT STRIP_TAC
    >> Cases_on `c= h`)

  >- (`get_cand_pile h p1 = get_cand_pile h p2` by metis_tac [piles_eq_list_def] >>
     (`MEM (h,l') p1 ==> MEM (h, l') p2` by (STRIP_TAC >>
     `get_cand_pile c p1 = l'` by
     metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
     GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
       `MEM (h,get_cand_pile h p2) p2` by
       metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
       GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
         `l' = get_cand_pile h p2` by
         metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
         GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
           metis_tac [MEM])) >>
     (`MEM (h,l') p2 ==> MEM (h,l') p1` by (STRIP_TAC >>
     `get_cand_pile c p2 = l'`
     by metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
     GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
       `MEM (h,get_cand_pile h p1) p1` by
       metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
       GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
         `l' = get_cand_pile h p1` by
         metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
         GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
            metis_tac [MEM])) >>
     metis_tac [MEM])
  >- (`list_MEM l1 (MAP FST p1)` by metis_tac [MEM,Logical_list_MEM_VICE_VERCA_TheFunctional] >>
      `list_MEM l1 (MAP FST p2)` by metis_tac [MEM,Logical_list_MEM_VICE_VERCA_TheFunctional] >>
      `piles_eq_list l1 l2 p1 p2` by metis_tac [piles_eq_list_def] >>
      metis_tac [MEM])));


val logical_to_functional_piles_eq = Q.store_thm ("logical_to_functional_piles_eq",
`! l1 l2 p1 p2.  (!c. MEM c l1 ==> (~ MEM c l2 ==> (!l'. MEM (c,l') p1 <=> MEM (c,l') p2)))
              /\ (ALL_DISTINCT (MAP FST p1)) /\ (ALL_DISTINCT (MAP FST p2) )
              /\ (!d. MEM d l1 ==> MEM d (MAP FST p1) /\ MEM d (MAP FST p2)) ==> piles_eq_list l1 l2 p1 p2`,

  Induct_on `l1`
    >- rw[piles_eq_list_def]
    >- (REPEAT STRIP_TAC
     >> rw[piles_eq_list_def]
      >> `!l'. MEM (h,l') p1 <=> MEM (h,l') p2` by FULL_SIMP_TAC list_ss [MEM]
       >> metis_tac [GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE,MEM]));


val functional_to_logical_update_pile = Q.store_thm ("functional_to_logical_update_pile",
 `! (qu: rat) (t: (cand # rat) list) l p1 p2. (ALL_DISTINCT (MAP FST p1)) /\ (ALL_DISTINCT (MAP FST p2))
        /\   (update_cand_pile qu t l p1 p2) ==>
              (!c. MEM c l ==> (!l'. MEM (c,l') p2 ==>
                                         (MAP FST l' = MAP FST (get_cand_pile c p1))
                                      /\ (MAP SND l' = update_cand_trans_val qu c t p1)))`,

   Induct_on `l`
     >- rw[]
     >- (REPEAT STRIP_TAC
       >- (FULL_SIMP_TAC list_ss []
          >- (`? l1 l2. p2 = l1 ++ (c,l') ::l2` by metis_tac [MEM,MEM_SPLIT]
           >> `MAP FST p2 = (MAP FST l1) ++ c :: (MAP FST l2)` by FULL_SIMP_TAC list_ss [FST,MAP_APPEND_TRIO]
            >> `MEM c (MAP FST p2)` by FULL_SIMP_TAC list_ss [MEM_APPEND]
             >> `l' = get_cand_pile h p2` by metis_tac [GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE]
              >> metis_tac [update_cand_pile_def])
          >- metis_tac [update_cand_pile_def])
       >- (FULL_SIMP_TAC list_ss []
         >- (`? l1 l2. p2 = l1 ++ (c,l') ::l2` by metis_tac [MEM,MEM_SPLIT]
          >> `MAP FST p2 = (MAP FST l1) ++ c :: (MAP FST l2)` by FULL_SIMP_TAC list_ss [FST,MAP_APPEND_TRIO]
           >> `MEM c (MAP FST p2)` by FULL_SIMP_TAC list_ss [MEM_APPEND]
            >> `l' = get_cand_pile h p2` by metis_tac [GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE]
             >> metis_tac[update_cand_pile_def])
       >- metis_tac [update_cand_pile_def])));



val logical_to_functional_update_pile = Q.store_thm ("logical_to_functional_update_pile",
 `! (qu: rat) (t: (cand #rat) list) l p1 p2. (!c. MEM c l ==> MEM c (MAP FST p2)) /\
                                            (!c. MEM c l ==> (!l'. MEM (c,l') p2 ==>
                                              (MAP FST l' = MAP FST (get_cand_pile c p1))
                                                /\ (MAP SND l' = update_cand_trans_val qu c t p1))) ==>
                                                    (update_cand_pile qu t l p1 p2)`,

    Induct_on `l`
      >- rw [update_cand_pile_def]
      >- ((REPEAT STRIP_TAC
       >> rw[update_cand_pile_def])
          >- (`MEM (h,get_cand_pile h p2) p2` by metis_tac [MEM,GET_CAND_PILE_MEM]
            >> metis_tac [MEM])
          >- (`MEM (h,get_cand_pile h p2) p2` by metis_tac [MEM,GET_CAND_PILE_MEM]
            >> metis_tac [MEM])));


val tally_comparison_total = Q.store_thm ("tally_comparison_total",
 `!t c1 c2. ((tally_comparison t) c1 c2) \/ ((tally_comparison t) c2 c1)`,
  ((REPEAT STRIP_TAC
    >> rw[tally_comparison_def]
     >> ASSUME_TAC RAT_LES_TOTAL
      >> first_assum (qspecl_then [`get_cand_tally c1 t`,`get_cand_tally c2 t`] strip_assume_tac))
         >- (DISJ1_TAC
          >> metis_tac [RAT_LES_IMP_LEQ])
         >- (DISJ1_TAC
          >> metis_tac [RAT_LEQ_REF])
         >- (DISJ2_TAC
          >> metis_tac [RAT_LES_IMP_LEQ])));


val tally_comparison_total_COR = Q.store_thm ("tally_comparison_total_COR",
 `!t. total (tally_comparison t)`,

   (ASSUME_TAC (INST_TYPE [alpha |-> ``:cand``] total_def)
     >> STRIP_TAC
       >> first_assum (qspecl_then [`tally_comparison t`] strip_assume_tac)
         >> metis_tac [tally_comparison_total]));



val tally_comparison_trans = Q.store_thm ("tally_comparison_trans",
 `!t. transitive (tally_comparison t)`,

   (STRIP_TAC
     >> `! c1 c2 c3. (tally_comparison t) c1 c2 /\ (tally_comparison t) c2 c3 ==> (tally_comparison t) c1 c3`
       by (REPEAT STRIP_TAC
        >> metis_tac [tally_comparison_def,RAT_LEQ_TRANS])
          >> metis_tac[transitive_def]));

(* to be constructed

val Logical_to_Functional_elect = Q.store_thm ("Logical_to_Functional_elect",
 `! st (qu: rat) l j1 j2. elect st qu l j1 j2 ==> Elect_dec st qu l (j1,j2)`,

(rw [elect,Elect_dec]
  >> EVAL_TAC
   >> `take_append (bl ++ l1) bl = l1` by metis_tac [take_append,take_append_returns_appended]
    >> REPEAT STRIP_TAC)
       >- metis_tac []
       >- metis_tac [NO_DUP_PRED_to_no_dup]
       >- (RW_TAC bool_ss []
         >> metis_tac [list_nchotomy,non_empty])
       >- (RW_TAC bool_ss []
         >> `!c. MEM c l1 ==> MEM c (MAP FST t)` by metis_tac [MEM, Valid_PileTally]
           >> metis_tac [logical_to_functional_BiggerThanQuota,bigger_than_quota,MEM])
       >- FULL_SIMP_TAC list_ss [LENGTH_APPEND]
       >- metis_tac [logical_to_functional_eqe_list_dec]
       >- metis_tac [eqe_list_dec2_verified]
       >- metis_tac [NO_DUP_PRED_to_no_dup]
       >- metis_tac [NO_DUP_PRED_to_no_dup]
       >- metis_tac [NO_DUP_PRED_to_no_dup]
       >- metis_tac [logical_to_functional_eqe_list_dec]
       >- metis_tac [eqe_list_dec2_verified]
       >- (`!d. MEM d h ==> MEM d (MAP FST p) /\ MEM d (MAP FST np)` by metis_tac [MEM,Valid_PileTally]
         >> metis_tac [logical_to_functional_piles_eq])
       >- metis_tac [NO_DUP_PRED_to_no_dup]
       >- metis_tac [NO_DUP_PRED_to_no_dup]
       >- metis_tac [NO_DUP_PRED_to_no_dup]
       >- metis_tac [Valid_Init_CandList,list_nchotomy,non_empty]
       >- metis_tac [Valid_Init_CandList,NO_DUP_PRED_to_no_dup]
       >- RW_TAC bool_ss []
       >- metis_tac [Valid_PileTally,PileTally_to_PileTally_DEC1]
       >- metis_tac [Valid_PileTally,PileTally_to_PileTally_DEC2]
       >- metis_tac [Valid_PileTally,PileTally_to_PileTally_DEC1]
       >- metis_tac [Valid_PileTally,PileTally_to_PileTally_DEC2]
       >- metis_tac [Valid_PileTally,PileTally_to_PileTally_DEC1]
       >- metis_tac [Valid_PileTally,PileTally_to_PileTally_DEC2]
       >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND]
       >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND]
       >- (`(!c. MEM c l1 ==> MEM c (MAP FST np))` by metis_tac [MEM,Valid_PileTally]
         >> `(!c. MEM c l ==> MEM c (MAP FST p))` by metis_tac [MEM,Valid_PileTally]
           >> metis_tac [logical_to_functional_update_pile]));

*)

(* to be reconstructed


val Functional_to_Logical_elect = Q.store_thm ("Functional_to_Logical_elect",
 `! st qu l j1 j2. Elect_dec st qu l (j1,j2) ==> elect st qu l j1 j2`,

 (REPEAT STRIP_TAC
  >> rw[elect]
    >> Cases_on `j1`)

  >- (Cases_on `j2`

     >- ((Cases_on `p` >> Cases_on `r` >> Cases_on `r'` >> Cases_on `r` >> Cases_on `r'`
      >> Cases_on `p'` >> Cases_on `r'` >> Cases_on `r''` >> Cases_on `r'` >> Cases_on `r''`
       >> rfs[Elect_dec]
        >> MAP_EVERY qexists_tac [`take_append q'''''''' q'''`]
          >> REPEAT STRIP_TAC)

          >- metis_tac [non_empty]
          >- RW_TAC bool_ss []
          >- metis_tac [functional_to_logical_BiggerThanQuota]
          >- rw []
          >- metis_tac [eqe_list_dec_MEM1,MEM,no_dup_IMP_NO_DUP_PRED]
          >- metis_tac [eqe_list_dec_MEM1,MEM,no_dup_IMP_NO_DUP_PRED]
          >- metis_tac [eqe_list_dec2_verified,MEM]
          >- metis_tac [no_dup_IMP_NO_DUP_PRED]
          >- metis_tac [no_dup_IMP_NO_DUP_PRED]
          >- metis_tac [no_dup_IMP_NO_DUP_PRED]
          >- metis_tac [no_dup_IMP_NO_DUP_PRED]
          >- metis_tac [eqe_list_dec_MEM1,MEM,no_dup_IMP_NO_DUP_PRED]
          >- metis_tac [eqe_list_dec_MEM1,MEM,no_dup_IMP_NO_DUP_PRED]
          >-  metis_tac [eqe_list_dec2_verified]
          >- (`!c. MEM c r ==> MEM c l` by metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional]
            >> `!c. MEM c r ==> MEM c (MAP FST q'')`
                by metis_tac [Valid_PileTally,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally,MEM]
              >> `!c. MEM c r ==> MEM c (MAP FST q''''''')`
                   by metis_tac [Valid_PileTally,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally,
                    MEM,Logical_list_MEM_VICE_VERCA_TheFunctional]
                >> metis_tac[Logical_list_MEM_VICE_VERCA_TheFunctional,functional_to_logicl_piles_eq
                    ,no_dup_IMP_NO_DUP_PRED])
          >- metis_tac [no_dup_IMP_NO_DUP_PRED]
          >- metis_tac [no_dup_IMP_NO_DUP_PRED]
          >- metis_tac [no_dup_IMP_NO_DUP_PRED]
          >- metis_tac [functional_to_logical_update_pile,no_dup_IMP_NO_DUP_PRED]
          >-  metis_tac [functional_to_logical_update_pile,no_dup_IMP_NO_DUP_PRED]
          >- metis_tac [no_dup_IMP_NO_DUP_PRED,non_empty,Valid_Init_CandList]
          >- metis_tac [Valid_PileTally,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
          >-  metis_tac [Valid_PileTally,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
          >- metis_tac [Valid_PileTally,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
          >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional]
          >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional]
          >- RW_TAC bool_ss [])

     >- rfs [Elect_dec])

  >- (Cases_on `j2`

   >- rfs [Elect_dec]
   >- rfs [Elect_dec]));

*)

val Initial_Judgement_IMP_TheLogical = Q.store_thm ("Initial_Judgement_IMP_TheLogical",
 `! l j. Initial_Judgement_dec l j ==> initial_judgement l j`,

  (REPEAT STRIP_TAC >> rw[initial_judgement_def]
    >> Cases_on `j`)

     >- (PairCases_on `p`
        >> MAP_EVERY qexists_tac [`p0`,`p1`,`p2`]
           >>  rfs[Initial_Judgement_dec_def,EVERY_MEM]
             >>  metis_tac[NULL_EQ])
     >- metis_tac[Initial_Judgement_dec_def]);


val Logical_to_Functional_Initial_Judgement = Q.store_thm ("Logical_to_Functional_Initial_Judgement",
 `! l j. initial_judgement l j ==> Initial_Judgement_dec l j`,

  (REPEAT STRIP_TAC
    >> rfs [initial_judgement_def]
      >> rw[Initial_Judgement_dec_def])
         >- FULL_SIMP_TAC list_ss [EVERY_MEM]
         >- FULL_SIMP_TAC list_ss [EVERY_MEM]);


(*
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


*)

(*
val Logical_to_computational_checker= Q.store_thm("Logical_to_computatonal_checker",
 `! st qu l J. valid_judgement st qu l J ==> CHECKER_AUX_dec st qu l J`,

  Induct_on `J`
    >- rw [checker_aux2_def]
    >- ((REPEAT STRIP_TAC >>
        `(J = []) \/ (J <> [])` by metis_tac [list_nchotomy])
           >- (rfs[Checker_Aux2_dec,checker_aux2_def]
            >> FULL_SIMP_TAC list_ss [LAST_DEF]
             >> metis_tac [final_judgement,Final_Judgement_dec])
           >- ((`? j' J'. (J = j'::J')` by metis_tac[list_nchotomy]
                 >> RW_TAC bool_ss []
                  >> rw[Checker_Aux2_dec])
            >- ((rfs[checker_aux2_def]
             >> first_assum (qspecl_then [`[]`,`J'`,`h`,`j'`] strip_assume_tac)
              >> `h::j'::J' = [] ++ [h;j'] ++ J'` by EVAL_TAC
               >> `  (hwin qu st h j')
                 \/ (ewin qu st h j')
                 \/ (Count_Aux st qu l h j')
                 \/ (transfer st qu l h j')
                 \/ (elect st qu l h j')
                 \/ (? c. MEM c l /\ elim_cand st qu l c h j')` by metis_tac [])
                   >- metis_tac [hwin_to_Hwin]
                   >- metis_tac [ewin_to_Ewin_thm]
                   >- metis_tac [Count_Aux_IMP_Count_Aux_dec]
                   >- metis_tac [Logical_transfer_to_Functional_Transfer]
                   >- metis_tac [Logical_to_Functional_elect]
                   >- (ASSUME_TAC (INST_TYPE [alpha |-> ``:Cand``] MEM_SPLIT)
                     >> first_x_assum (qspecl_then [`c`,`l`] strip_assume_tac)
                       >> `? l1 l2. l = l1 ++ c:: l2` by metis_tac []
                        >> RW_TAC bool_ss [Elim_dec] >> REPEAT DISJ2_TAC
                          >> rw [EXISTS_DEF]
                           >> DISJ2_TAC >> DISJ1_TAC
                            >> metis_tac [Elim_dec,Logical_elim_to_Functional_Elim]))


             >- (rfs[checker_aux2_def]
              >> first_assum (qspecl_then [`st`,`qu`,`l`] strip_assume_tac)
               >> `! J0 J1 j0 j1. (j'::J' = J0 ++ [j0;j1] ++ J1) ==>  (hwin qu st j0 j1)
                                                     \/ (ewin qu st j0 j1)
                                                     \/ (Count_Aux st qu l j0 j1)
                                                     \/ (transfer st qu l j0 j1)
                                                     \/ (elect st qu l j0 j1)
                                                     \/ (? c. MEM c l /\ elim_cand st qu l c j0 j1)`
                  by  (REPEAT STRIP_TAC
                  >> first_assum (qspecl_then [`h::J0`,`J1`,`j0`,`j1`] strip_assume_tac)
                   >> `h::j'::J' = h::J0 ++ [j0;j1] ++J1` by FULL_SIMP_TAC list_ss[]
                     >> metis_tac [])
                       >> metis_tac []))));

*)

val _ = export_theory();
