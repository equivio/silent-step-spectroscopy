(* All sessions must be in chapter AFP *)
chapter AFP

(* There must be one session with the (short) name of the entry.
   This session generates the web document and HTML files.

   It is strongly encouraged to have precisely one session, but it
   if needed, further sessions are permitted.

   Every theory must be included in at least one of the sessions.
*)

(* Session name, list base session: *)
session LinearTimeBranchingTimeSpectroscopyAccountingForSilentSteps = HOL +
  (* Timeout (in sec) in case of non-termination problems *)
  options [timeout = 600, quick_and_dirty = true]

  sessions
    "HOL-Lattice"
    "HOL-Library"

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
    HML_Context
    LTS_Prime
    Example_Instantiation

(* Dependencies on document source files: *)
  document_files
    "change_index.tex"
    "conclusion.tex"
    "introduction.tex"
    "outcomes.tex"
    "root.bib"
    "root.tex"
