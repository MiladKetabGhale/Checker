open preamble CheckerTheory CheckerSpecTheory myparserTheory
 
* --------------------------------------------------------------------------------------*
* correct order of the rules which must be applied to get a "valide certificate" output *


* line 5 to line 4   -------> EWIN_dec *
* line 6 to line 5   -------> ELECT_dec *
* line 7 to line 6   -------> COUNT_dec *
* line 8 to line 7   -------> ELIM_CAND_dec *
* line 9 to line 8   -------> COUNT_dec *


* ----------------------------------------------------------------------------- *
* In the following, we try EVAL on each of the above steps to see what happens *


* --------- line 5 to line 4 -------------------------------------- *

 
EVAL ``EWIN_dec (7 / 2, 1, [Cand (strlit "A"); Cand (strlit "B"); Cand (strlit "C")])
(THE (parse_judgement (strlit
"[]; A{4%1} B{1%1} C{1%1}; A{[([A,C],1%8),([A,B,C],1%8),([A,C,B],1%8),([B,A],1%8)]} B{[]} C{[([C,B,A],1%1)]}; [A]; [A]; [C]\n")))

(Final (THE (parse_candidates (strlit "[A]\n"))))``



* ---------line 6 to line 5 ----------------------------------------- *
 
EVAL ``ELECT_dec  (7 / 2, 1, [Cand (strlit "A"); Cand (strlit "B"); Cand (strlit "C")])
(THE (parse_judgement (strlit
"[]; A{4%1} B{1%1} C{1%1}; A{[([A,C],1%1),([A,B,C],1%1),([A,C,B],1%1),([B,A],1%1)]} B{[]} C{[([C,B,A],1%1)]}; []; []; [A,C]\n")))

(THE (parse_judgement (strlit
"[]; A{4%1} B{1%1} C{1%1}; A{[([A,C],1%8),([A,B,C],1%8),([A,C,B],1%8),([B,A],1%8)]} B{[]} C{[([C,B,A],1%1)]}; [A]; [A]; [C]\n")))``
  

* ------------ line 7 to line 6 ----------------------------------- *
 
EVAL ``COUNT_dec  (7 / 2, 1, [Cand (strlit "A"); Cand (strlit "B"); Cand (strlit "C")])
(THE (parse_judgement (strlit
"[([B,A],1%1)]; A{3%1} B{1%1} C{1%1}; A{[([A,C],1%1),([A,B,C],1%1),([A,C,B],1%1)]} B{[]} C{[([C,B,A],1%1)]}; []; []; [A,C]\n")))

(THE (parse_judgement (strlit
"[]; A{4%1} B{1%1} C{1%1}; A{[([A,C],1%1),([A,B,C],1%1),([A,C,B],1%1),([B,A],1%1)]} B{[]} C{[([C,B,A],1%1)]}; []; []; [A,C]\n")))``


* ------------- line 8 to line 7 ----------------------------------- *
 
EVAL ``ELIM_CAND_dec  (Cand (strlit "B")) (7 / 2, 1, [Cand (strlit "A"); Cand (strlit "B"); Cand (strlit "C")])

(THE (parse_judgement (strlit
"[]; A{3%1} B{1%1} C{1%1}; A{[([A,C],1%1),([A,B,C],1%1),([A,C,B],1%1)]} B{[([B,A],1%1)]} C{[([C,B,A],1%1)]}; []; []; [A,B,C]\n")))

(THE (parse_judgement (strlit
"[([B,A],1%1)]; A{3%1} B{1%1} C{1%1}; A{[([A,C],1%1),([A,B,C],1%1),([A,C,B],1%1)]} B{[]} C{[([C,B,A],1%1)]}; []; []; [A,C]\n")))``

 
* ----------------- line 9 to line 8 ----------------------------- *

EVAL ``COUNT_dec  (7 / 2, 1, [Cand (strlit "A"); Cand (strlit "B"); Cand (strlit "C")])

(THE (parse_judgement (strlit
"[([A,C],1%1),([A,B,C],1%1),([A,C,B],1%1),([B,A],1%1),([C,B,A],1%1)]; A{0%1} B{0%1} C{0%1}; A{[]} B{[]} C{[]}; []; []; [A,B,C]\n")))

(THE (parse_judgement (strlit
"[]; A{3%1} B{1%1} C{1%1}; A{[([A,C],1%1),([A,B,C],1%1),([A,C,B],1%1)]} B{[([B,A],1%1)]} C{[([C,B,A],1%1)]}; []; []; [A,B,C]\n")))``