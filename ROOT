(* All sessions must be in chapter AFP *)
chapter AFP

(* There must be one session with the (short) name of the entry.
   This session generates the web document and HTML files.

   It is strongly encouraged to have precisely one session, but it
   if needed, further sessions are permitted.

   Every theory must be included in at least one of the sessions.
*)

(* Session name, list base session: *)
session Weak_Spectroscopy = "HOL-Library" +
  (* Timeout (in sec) in case of non-termination problems *)
  options [timeout = 720, quick_and_dirty = false]

(* To suppress document generation of some theories: *)
(*
  theories [document = false]
    This_Theory
    That_Theory
*)

(* The top-level theories of the submission: *)
  theories
    Silent_Step_Spectroscopy
    Weak_Traces
    Branching_Bisimilarity
    Example_Instantiation

(* Dependencies on document source files: *)
  document_files
    "introduction.tex"
    "conclusion.tex"
    "root.bib"
    "root.tex"
