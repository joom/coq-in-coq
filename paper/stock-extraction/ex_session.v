Require Extraction.
Extraction Language OCaml.

Inductive St : Set := Ready : St | Sent : St | Done : St.
Inductive Msg : Set := greeting : Msg.

Inductive Chan : St -> Set := mkchan : forall s : St, Msg -> Chan s.

Definition open : Chan Ready := mkchan Ready greeting.

Definition send (m : Msg) (c : Chan Ready) : Chan Sent := mkchan Sent m.

Definition getmsg {s} (c : Chan s) : Msg := match c with mkchan _ m => m end.

Definition recv (c : Chan Sent) : Chan Done := mkchan Done (getmsg c).

Definition close (c : Chan Done) : Msg := getmsg c.

Definition run (req : Msg) : Msg := close (recv (send req open)).

Definition client (req : Msg) (c : Chan Ready) : Msg := close (recv (send req c)).

Definition sendStep (req : Msg) (c : Chan Ready) : Chan Sent := send req c.

Extraction "ex_session.ml" run client sendStep.
