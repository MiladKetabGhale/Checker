(*
  This theory creates a CakeML program implementing the Checker_Aux2_dec HOL
  function via proof-producing translation.
*)
open preamble basis CheckerTheory

val _ = new_theory "CheckerProg";

val _ = translation_extends"basisProg";

val r = translate get_cand_tally_def;

val r = translate empty_list_def;
val r = translate non_empty_def;
val r = translate not_elem_def;
val r = translate no_dup_def;

val r = translate less_than_quota_def;
val r = translate remove_one_cand_def;
val r = translate bigger_than_cand_def;
val r = translate get_cand_pile_def;

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

val () = use_mem_intro := true;
val r = translate list_MEM_def;

val r = translate Valid_PileTally_DEC1_def;
val r = translate Valid_PileTally_DEC2_def;
val r = translate subpile1_def;
val r = translate subpile2_def;
val r = translate Elim_cand_dec_def;
val () = use_mem_intro := false;

val r = translate Elim_dec_def;

val r = translate Final_Judgement_dec_def;

val r = translate sum_aux_def;

val () = use_mem_intro := true;
val r = translate fcc_def;
val r = translate Count_Dec_Aux_def;
val r = translate Transfer_dec_def;
val r = translate eqe_list_dec_def;
val r = translate eqe_list_dec2_def;
val r = translate piles_eq_list_def;
val () = use_mem_intro := false;

val r = translate Count_Aux_dec_def;
val r = translate Hwin_def;
val r = translate Ewin_def;
val r = translate take_append_def;
val r = translate SORTED_DEF;
val r = translate tally_comparison_def;
val r = translate bigger_than_quota_def;

val r = translate update_cand_trans_val_def;
val r = translate update_cand_pile_def;
val r = translate Elect_dec_def;

val elect_dec_side = Q.prove(
  `elect_dec_side a b c d = T`,
  rw[definition"elect_dec_side_def"]
  \\ cheat (* wait for update to translator *)
  ) |> update_precondition;

val r = translate Checker_Aux2_dec_def;

val r = translate all_elem_nil_def;
val r = translate all_elem_zero_def;

val r = translate Initial_Judgement_dec_def;

val r = translate Check_Parsed_Certificate_def;

val _ = export_theory();
