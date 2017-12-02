(*
  This theory creates a CakeML program implementing the Checker_Aux2_dec HOL
  function via proof-producing translation.
*)
open preamble basis CheckerTheory CheckerSpecTheory

val _ = new_theory "CheckerProg";

val _ = translation_extends"basisProg";

(* TODO: this should be moved to CakeML *)
val r = translate NULL;
(* -- *)

val r = translate SUM_RAT_def;

val r = translate get_cand_tally_def;

val r = translate less_than_quota_def;
val r = translate equal_except_dec_def;
val r = translate bigger_than_cand_def;
val r = translate get_cand_pile_def;

val () = use_mem_intro := true;
val r = translate list_MEM_dec_def;

val r = translate Valid_PileTally_dec1_def;
val r = translate Valid_PileTally_dec2_def;
val r = translate subpile1_def;
val r = translate subpile2_def;
val r = translate ELIM_CAND_dec_def;

val r = translate first_continuing_cand_dec_def;
val r = translate COUNTAux_dec_def;
val r = translate COUNT_dec_def;

val r = translate TRANSFER_dec_def;

val r = translate eqe_list_dec_def;
val r = translate eqe_list_dec2_def;
val r = translate piles_eq_list_def;

val () = use_mem_intro := false;

val r = translate HWIN_dec_def;
val r = translate EWIN_dec_def;

val r = translate take_append_def;

val r = translate SORTED_DEF;
val r = translate tally_comparison_def;
val r = translate bigger_than_quota_def;

val r = translate update_cand_trans_val_def;
val r = translate update_cand_pile_def;
val r = translate ELECT_dec_def;

val update_cand_trans_val_side_def = fetch"-""update_cand_trans_val_side_def";
val update_cand_pile_side_def = fetch"-""update_cand_pile_side_def";

val update_cand_pile_side = Q.prove(
  `∀c a b d e.
    EVERY(λx. get_cand_tally x b ≠ 0) c ⇒
    update_cand_pile_side a b c d e`,
  Induct
  \\ rw[Once update_cand_pile_side_def,update_cand_trans_val_side_def]);

val elect_dec_side = Q.prove(
  `elect_dec_side a b c = T`,
  rw[definition"elect_dec_side_def"]
  \\ match_mp_tac update_cand_pile_side
  \\ fs[bigger_than_quota_def,EVERY_MEM]
  \\ rw[] \\ res_tac
  \\ strip_tac \\ fs[]
  \\ imp_res_tac ratTheory.RAT_LES_LEQ_TRANS
  \\ fs[]) |> update_precondition;

val r = translate Initial_Judgement_dec_def;

val r = translate Valid_Step_def;

(* To see the code:
val () = astPP.enable_astPP()

val Prog_thm =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def];

val () = astPP.disable_astPP()
*)

val _ = export_theory();
