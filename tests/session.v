(* Session-typed / typestate protocols in the Calculus of Constructions.

   [Chan s] is a communication channel currently in protocol state [s].  The
   operations are indexed by state, so the protocol's ORDERING is enforced by
   the type system: a channel must be [Ready] to [send], [Sent] before you can
   [recv], and [Done] before you can [close].  Calling [recv] on a fresh
   channel, or [close] twice, is a type error -- an illegal protocol run is
   simply not typeable.

   Extraction erases the state index: [Chan s] becomes the plain type [Chan],
   and the protocol operations become ordinary function calls.  The session
   discipline is compile-time only.  This is exactly the boundary gradual
   typing addresses: the erased channel is what an untyped peer would hold, and
   the verified extraction shows the typed client compiles to it faithfully. *)


Axiom St : Set.
Axiom Ready : St.        (* may send   *)
Axiom Sent  : St.        (* may recv   *)
Axiom Done  : St.        (* may close  *)

Axiom Msg : Set.
Axiom Chan : St -> Set.

Axiom open  : Chan Ready.
Axiom send  : Msg -> Chan Ready -> Chan Sent.
Axiom recv  : Chan Sent -> Chan Done.
Axiom close : Chan Done -> Msg.          (* yields the received reply *)


(* the one legal run of the protocol: open, send, recv, close.
   Inferred type is just Msg -> Msg: send a request, get a reply. *)

Infer fun (req : Msg) => close (recv (send req open)).

Extract fun (req : Msg) => close (recv (send req open)).


(* a client abstract over its starting channel rather than opening one:
   works in any Ready channel and drives it to a reply. *)

Extract fun (req : Msg) (c : Chan Ready) => close (recv (send req c)).


(* just the send step, exposing the state transition Ready -> Sent. *)

Extract fun (req : Msg) (c : Chan Ready) => send req c.


(* the receive-then-close tail, from a Sent channel to the final Msg. *)

Extract fun (c : Chan Sent) => close (recv c).
