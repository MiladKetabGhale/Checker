(*
  Simple wordcount program, to demonstrate use of CF.
*)

open preamble
     ml_translatorLib cfTacticsLib
     basisProgTheory basisFunctionsLib ioProgLib
     cfLetAutoLib
     splitwordsTheory
     myparserTheory


val _ = new_theory"testing";

val _ = translation_extends"basisProg";
  
val wc_lines_def = Define`
  wc_lines lines = SUM (MAP (LENGTH o splitwords) lines)`;
     
     
val non_empty_def = Define `
      non_empty (J: judgement list) =
        case J of
           [] => (0: num)
         | _  => 1`   
      
val my_wc_def = Define `
  my_wc lines = non_empty (MAP (parse_whole_line) (splitlines lines))`
         
       
          
val res = translate splitwords_def;
val res = translate wc_lines_def;
         
val res = translate parse_whole_line_def; 
val res = translate my_wc_def;
   
val wordcount = process_topdecs`
  fun wordcount u =
    case FileIO.inputLinesFrom (List.hd (Commandline.arguments()))
    of SOME lines =>
      (print (Bool.toString ((all_state (MAP parse_whole_line (splitlines lines))))); print "\n")`;
           
val res = translate non_empty_def;
val res = translate SPLITP;      
val res = translate NULL; 
val res = translate TOKENS_def;     
val res = translate EXPLODE_def;    
val res = translate STR_def;  
val res = translate process_chunk_def;
val res = translate split_it_into_pair_def;
val res = translate IMPLODE_def; 
val res = translate parse_pair_t_def;    
val res = translate parse_pair_def;     
val res = translate cand_list;
val res = translate parse_first_part_def; 
val res = translate parse_whole_line_def; 
val res =translate my_wc_def;
 
val _ = append_prog wordcount;
        
val wordcount_spec = Q.store_thm("wordcount_spec",
  `hasFreeFD fs ∧ inFS_fname fs fname ∧
   cl = [explode pname; explode fname] ∧
   contents = THE (ALOOKUP fs.files fname)
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "wordcount" (get_ml_prog_state()))
     [uv] (COMMANDLINE cl * ROFS fs * STDOUT out)
     (POSTv uv. &UNIT_TYPE () uv * ROFS fs * COMMANDLINE cl *
                 STDOUT (out ++ (Bool.toString (all_state (MAP parse_whole_line (splitlines contents)))) ++ "\n"))`,
  strip_tac \\    
  xcf "wordcount" (get_ml_prog_state()) \\    
  xlet_auto >- (xcon \\ xsimpl) \\      
  xlet_auto >- xsimpl \\    
  xlet_auto >- xsimpl \\   
  (* we will need to know wfcl cl to prove that fname is a valid filename.
     this comes from the COMMANDLINE precondition.
     `wfcl cl` by ... wouldn't work because the current goal is needed to do the xpull on *)
  reverse(Cases_on`wfcl cl`) >- (rfs[mlcommandLineProgTheory.COMMANDLINE_def] \\ xpull) \\ 
  xlet_auto >- (  
    xsimpl \\  
    rfs[mlcommandLineProgTheory.wfcl_def,commandLineFFITheory.validArg_def,
        EVERY_MEM,mlstringTheory.LENGTH_explode] ) \\    
  xmatch \\ fs[ml_translatorTheory.OPTION_TYPE_def] \\   
  reverse conj_tac >- (EVAL_TAC \\ fs[]) \\     
  xlet_auto >- xsimpl \\   
  xlet_auto >- xsimpl \\     
  xlet_auto >- ( (* TODO: xapp could be smarter and instantiate this *)
    xsimpl \\
    CONV_TAC SWAP_EXISTS_CONV \\
    qexists_tac`out` \\ xsimpl ) \\     
  xlet_auto >- ( (* same xapp issue *)
    xsimpl \\
    CONV_TAC SWAP_EXISTS_CONV \\
    qexists_tac`out` \\ xsimpl ) \\ (*Milad:here seems to be the end of first line topdec*) 
  xlet_auto >- xsimpl \\  
  xlet_auto >- xsimpl \\      
  xlet_auto >- ( (* same xapp issue *) 
    xsimpl \\ 
    CONV_TAC SWAP_EXISTS_CONV \\
    qexists_tac`out` \\ xsimpl ) \\      
  xapp \\ xsimpl \\ (* same xapp issue *)      
  qmatch_goalsub_abbrev_tac`STDOUT output` \\    
  CONV_TAC SWAP_EXISTS_CONV \\  
  qexists_tac`output` \\ xsimpl \\       
  qmatch_goalsub_abbrev_tac`STDOUT (output'++"\n") * GC` \\   
  `output = output'` suffices_by xsimpl \\ 
  simp[Abbr`output`,Abbr`output'`] \\ 
  simp[wc_lines_def] \\ 
  qmatch_abbrev_tac`s1 ++ " " ++ s2 = t1 ++ " " ++ t2` \\ 
  `s1 = t1 ∧ s2 = t2` suffices_by rw[] \\ 
  simp[Abbr`s1`,Abbr`t1`,Abbr`s2`,Abbr`t2`] \\
  simp[mlintTheory.toString_thm,integerTheory.INT_ABS_NUM] \\ 
  reverse conj_tac >- simp[mlfileioProgTheory.all_lines_def] \\
  simp[GSYM MAP_MAP_o,GSYM LENGTH_FLAT,splitwords_all_lines] \\ 
  simp[splitwords_def,mlstringTheory.TOKENS_eq_tokens_sym]);
 
val spec = wordcount_spec |> UNDISCH_ALL |> add_basis_proj
val name = "wordcount"
val (sem_thm,prog_tm) = call_thm (get_ml_prog_state()) name spec

val wordcount_prog_def = mk_abbrev"wordcount_prog" prog_tm;

val wordcount_semantics = save_thm("wordcount_semantics",
  sem_thm
  |> PURE_REWRITE_RULE[GSYM wordcount_prog_def]
  |> DISCH_ALL
  |> Q.GENL[`cls`,`contents`]
  |> SIMP_RULE(srw_ss())[]
  |> SIMP_RULE std_ss [AND_IMP_INTRO]);

val _ = export_theory();


*this is copied definition for exercises*
*-----------------------------------------------------------------------*
val wordcount = process_topdecs`
  fun wordcount u =
    case FileIO.inputLinesFrom (List.hd (Commandline.arguments()))
    of SOME lines =>
      (print (Int.toString (wc_lines lines)); print "\n")`
      
(*;
       print (Int.toString (List.length lines)); print "\n")`;*)

val _ = append_prog wordcount;
      
val wordcount_spec = Q.store_thm("wordcount_spec",
  `hasFreeFD fs ∧ inFS_fname fs fname ∧
   cl = [explode pname; explode fname] ∧
   contents = THE (ALOOKUP fs.files fname)
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v "wordcount" (get_ml_prog_state()))
     [uv] (COMMANDLINE cl * ROFS fs * STDOUT out)
     (POSTv uv. &UNIT_TYPE () uv * ROFS fs * COMMANDLINE cl *
                 STDOUT (out ++ (toString (LENGTH (TOKENS isSpace contents))) ++ "\n"
      ))`,
  strip_tac \\  
  xcf "wordcount" (get_ml_prog_state()) \\ 
  xlet_auto >- (xcon \\ xsimpl) \\ 
  xlet_auto >- xsimpl \\ 
  xlet_auto >- xsimpl \\  
  (* we will need to know wfcl cl to prove that fname is a valid filename.
     this comes from the COMMANDLINE precondition. 
     `wfcl cl` by ... wouldn't work because the current goal is needed to do the xpull on *)
  reverse(Cases_on`wfcl cl`) >- (rfs[mlcommandLineProgTheory.COMMANDLINE_def] \\ xpull) \\
  xlet_auto >- (     
    xsimpl \\ 
    rfs[mlcommandLineProgTheory.wfcl_def,commandLineFFITheory.validArg_def,
        EVERY_MEM,mlstringTheory.LENGTH_explode] ) \\    
  xmatch \\ fs[ml_translatorTheory.OPTION_TYPE_def] \\ 
  reverse conj_tac >- (EVAL_TAC \\ fs[]) \\    
  xlet_auto >- xsimpl \\      
  xlet_auto >- xsimpl \\     
  xlet_auto >- ( (* TODO: xapp could be smarter and instantiate this *)
    xsimpl \\   
    CONV_TAC SWAP_EXISTS_CONV \\  
    qexists_tac`out` \\ xsimpl ) \\     (* at this point I get to cf_app for Lit "\n" *)
  (*
  xlet_auto >- ( (* same xapp issue *)  
    xsimpl \\ 
    CONV_TAC SWAP_EXISTS_CONV \\
    qexists_tac`out` \\ xsimpl ) \\ 
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\ 
  xlet_auto >- ( (* same xapp issue *)
    xsimpl \\
    CONV_TAC SWAP_EXISTS_CONV \\
    qexists_tac`out` \\ xsimpl ) \\ 
  *)
  xapp \\ xsimpl \\ (* same xapp issue *)       
  qmatch_goalsub_abbrev_tac`STDOUT output` \\     
  CONV_TAC SWAP_EXISTS_CONV \\    
  qexists_tac`output` \\ xsimpl \\            
  qmatch_goalsub_abbrev_tac`STDOUT (output'++"\n") * GC` \\   
  `output = output'` suffices_by xsimpl \\ 
  simp[Abbr`output`,Abbr`output'`] \\ 
  simp[wc_lines_def] \\  
  (*
  qmatch_abbrev_tac`s1 ++ " " ++ s2 = t1 ++ " " ++ t2` \\
  `s1 = t1 ∧ s2 = t2` suffices_by rw[] \\
  simp[Abbr`s1`,Abbr`t1`,Abbr`s2`,Abbr`t2`] \\
  *)
  simp[mlintTheory.toString_thm,integerTheory.INT_ABS_NUM] \\ 
  (* reverse conj_tac >- simp[mlfileioProgTheory.all_lines_def] \\
  *) 
  simp[GSYM MAP_MAP_o,GSYM LENGTH_FLAT,splitwords_all_lines] \\
  simp[splitwords_def,mlstringTheory.TOKENS_eq_tokens_sym]);  
 

*-----------------------end of the copied part------------------------------------*
